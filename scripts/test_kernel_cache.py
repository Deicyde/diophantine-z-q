"""Regressions for project-cache provenance in the pinned kernel workflow."""
import ast
import functools
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HEAD = 'a' * 40
KERNEL = (ROOT / '.github/workflows/kernel-lean.yml').read_text(encoding='utf-8')
STEPS = re.split(r'^      - name: ', KERNEL, flags=re.M)[1:]
RESTORES = [step for step in STEPS if re.search(r'uses: actions/cache(?:/restore)?@', step)]
SAVES = [step for step in STEPS if re.search(r'uses: actions/cache/save@', step)]


@functools.lru_cache(maxsize=None)
def exact_ref_output(ref):
    """Execute the actual pre-checkout shell guard, not a Python imitation."""
    step = next(step for step in STEPS if '\n        id: cache_ref\n' in step)
    script = step.split('        run: |\n', 1)[1]
    script = '\n'.join(line[10:] for line in script.splitlines())+'\n'
    bash = ('C:/Program Files/Git/bin/bash.exe' if os.name == 'nt' else shutil.which('bash'))
    if not bash or not Path(bash).is_file():
        raise AssertionError('Bash is required to test the actual workflow guard')
    with tempfile.TemporaryDirectory() as directory:
        output = Path(directory)/'output'
        env = dict(os.environ, GITHUB_REF=ref, GITHUB_OUTPUT=output.as_posix())
        env.pop('BASH_ENV', None)
        subprocess.run([bash, '--noprofile', '--norc', '-eo', 'pipefail', '-c', script],
                       env=env, cwd=directory, check=True, capture_output=True)
        result = output.read_text().strip()
        if result not in {'is_main=true', 'is_main=false'}:
            raise AssertionError('Unexpected cache guard output: '+result)
        return result.split('=', 1)[1]


def condition(step, ref, outcome='skipped', full_build='', event='workflow_dispatch', publish='true'):
    expression = re.search(r'^        if: (.*)$', step, re.M).group(1)
    for name, value in [('steps.cache_ref.outputs.is_main', exact_ref_output(ref)),
                        ('steps.verified_bundle.outputs.publish', publish),
                        ('github.ref', ref), ('github.event_name', event),
                        ('steps.scope.outcome', outcome), ('steps.scope.outputs.full_build', full_build)]:
        expression = expression.replace(name, repr(value))
    tree = ast.parse(expression.replace('&&', ' and ').replace('||', ' or '), mode='eval')
    # This workflow subset uses only strings, equality and Boolean combinations.
    # Model Actions' case-insensitive string equality, including legacy guards.
    def evaluate(node):
        if isinstance(node, ast.Expression):
            return evaluate(node.body)
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            return node.value
        if isinstance(node, ast.BoolOp):
            values = [evaluate(value) for value in node.values]
            if isinstance(node.op, ast.And):
                return all(values)
            if isinstance(node.op, ast.Or):
                return any(values)
        if isinstance(node, ast.Compare) and len(node.ops) == 1:
            left, right = evaluate(node.left), evaluate(node.comparators[0])
            equal = left.casefold() == right.casefold()
            if isinstance(node.ops[0], ast.Eq):
                return equal
            if isinstance(node.ops[0], ast.NotEq):
                return not equal
        raise AssertionError('Unhandled cache condition syntax')
    return evaluate(tree)


class KernelCacheTests(unittest.TestCase):
    def test_exact_ref_guard_runs_before_any_candidate_code(self):
        guard = next(i for i, step in enumerate(STEPS) if '\n        id: cache_ref\n' in step)
        checkout = next(i for i, step in enumerate(STEPS) if 'uses: actions/checkout@' in step)
        self.assertLess(guard, checkout)
        for ref, expected in [('refs/heads/main','true'), ('refs/heads/Main','false'),
                              ('refs/heads/MAIN','false'), ('REFS/HEADS/main','false')]:
            with self.subTest(ref=ref):
                self.assertEqual(exact_ref_output(ref), expected)

    def test_every_non_main_ref_skips_all_project_cache_actions(self):
        self.assertEqual(RESTORES, [])
        self.assertEqual(SAVES, [])
        publish = next(s for s in STEPS if s.startswith('Publish verified successful main build outputs'))
        refs = ['refs/heads/contributor-branch', 'refs/pull/133/merge',
                'refs/tags/main', 'refs/heads/main-other', 'refs/heads/Main', 'refs/heads/MAIN',
                'refs/heads/codex/protocol-b-kernel/133/'+HEAD+'/'+'b'*40]
        for ref in refs:
            with self.subTest(ref=ref):
                self.assertFalse(condition(publish, ref, event='push'))
                self.assertFalse(condition(publish, ref, event='workflow_dispatch'))

    def test_legacy_string_guard_reproduces_case_variant_failure(self):
        publish = next(s for s in STEPS if s.startswith('Publish verified successful main build outputs'))
        legacy = publish.replace("steps.cache_ref.outputs.is_main == 'true'", "github.ref == 'refs/heads/main'")
        for ref in ['refs/heads/Main', 'refs/heads/MAIN']:
            self.assertTrue(condition(legacy, ref))
            self.assertFalse(condition(publish, ref))

    def test_main_publication_requires_completed_bundle_and_main_event(self):
        publish = next(s for s in STEPS if s.startswith('Publish verified successful main build outputs'))
        for event in ('push', 'workflow_dispatch'):
            self.assertTrue(condition(publish, 'refs/heads/main', event=event))
            self.assertFalse(condition(publish, 'refs/heads/main', event=event, publish='false'))
        self.assertFalse(condition(publish, 'refs/heads/main', event='pull_request'))
        self.assertIn('include-hidden-files: true', publish)
        self.assertIn('kernel-main-build-${{ github.run_id }}-${{ github.run_attempt }}', publish)

    def test_selector_is_installed_from_main_before_candidate_checkout(self):
        names = [s.splitlines()[0] for s in STEPS]
        read = names.index('Read the protected main reuse driver')
        select = names.index('Select and download verified main outputs')
        checkout = names.index('Check out candidate')
        self.assertLess(read, select)
        self.assertLess(select, checkout)
        self.assertIn('ref: main', STEPS[read])
        self.assertIn('persist-credentials: false', STEPS[read])
        self.assertIn('persist-credentials: false', STEPS[checkout])
        self.assertIn('enabled=false', STEPS[select])
        self.assertIn('building cold', STEPS[select])
        self.assertIn('cp "$trusted/scripts/"kernel_build_*.py', STEPS[select])

    def test_reuse_never_skips_the_full_build_or_audit(self):
        names = [s.splitlines()[0] for s in STEPS]
        sequence = ['Prepare verified reuse without credentials', 'Build all kernel modules',
                    'Bind completed build to the prepared inputs', 'Replay all kernel proofs and exact targets',
                    'Bind full audit and prepare a main-only output bundle',
                    'Publish verified successful main build outputs']
        indices = [names.index(n) for n in sequence]
        self.assertEqual(indices, sorted(indices))
        for name in ('Build all kernel modules', 'Replay all kernel proofs and exact targets'):
            step = STEPS[names.index(name)]
            self.assertNotIn('cache-hit', step)
            self.assertNotIn('reuse_driver.outputs', step)
            self.assertIn('-u GH_TOKEN -u GITHUB_TOKEN', step)
            self.assertIn('-u ACTIONS_RUNTIME_TOKEN', step)
            self.assertIn('-u LAKE_CACHE_KEY', step)
        self.assertNotIn('--skip-build', KERNEL)

    def test_all_reuse_execution_respects_the_existing_scope_skip(self):
        for step in STEPS:
            if step.startswith(('Read the protected', 'Select and download', 'Prepare verified',
                                'Bind completed', 'Bind full audit')):
                self.assertIn("steps.scope.outcome != 'success' || steps.scope.outputs.full_build != 'false'", step)

    def test_contract_pins_this_workflow_and_this_test(self):
        contract = json.loads((ROOT / 'KERNEL_CONTRACT.json').read_bytes())
        self.assertEqual(contract['files']['.github/workflows/kernel-lean.yml'], hashlib.sha256(KERNEL.encode()).hexdigest())
        self.assertEqual(contract['files']['scripts/test_kernel_cache.py'], hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
        self.assertIn('python -B scripts/test_kernel_cache.py', KERNEL)


if __name__ == '__main__':
    unittest.main()
