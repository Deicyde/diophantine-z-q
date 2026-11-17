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


def condition(step, ref, outcome='skipped', full_build='', event='workflow_dispatch'):
    expression = re.search(r'^        if: (.*)$', step, re.M).group(1)
    for name, value in [('steps.cache_ref.outputs.is_main', exact_ref_output(ref)),
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
        self.assertEqual(len(RESTORES), 1)
        self.assertEqual(len(SAVES), 1)
        refs = ['refs/heads/contributor-branch', 'refs/pull/133/merge',
                'refs/tags/main', 'refs/heads/main-other', 'refs/heads/Main', 'refs/heads/MAIN',
                'refs/heads/codex/protocol-b-kernel/133/'+HEAD+'/'+'b'*40]
        for step in RESTORES+SAVES:
            self.assertIn('path: .lake/build', step)
            for ref in refs:
                for outcome, full in [('skipped',''), ('failure',''), ('success','true'), ('success','false')]:
                    with self.subTest(ref=ref, outcome=outcome, full=full):
                        self.assertFalse(condition(step, ref, outcome, full, event='push'))

    def test_legacy_string_guard_reproduces_case_variant_failure(self):
        legacy = RESTORES[0].replace("steps.cache_ref.outputs.is_main == 'true'", "github.ref == 'refs/heads/main'")
        for ref in ['refs/heads/Main', 'refs/heads/MAIN']:
            self.assertTrue(condition(legacy, ref))
            self.assertFalse(condition(RESTORES[0], ref))

    def test_main_restore_save_and_scope_skip_are_preserved(self):
        self.assertTrue(condition(RESTORES[0], 'refs/heads/main'))
        self.assertTrue(condition(RESTORES[0], 'refs/heads/main', 'success', 'true'))
        self.assertFalse(condition(RESTORES[0], 'refs/heads/main', 'success', 'false'))
        self.assertTrue(condition(SAVES[0], 'refs/heads/main', event='push'))
        self.assertFalse(condition(SAVES[0], 'refs/heads/main'))

    def test_contract_pins_this_workflow_and_this_test(self):
        contract = json.loads((ROOT / 'KERNEL_CONTRACT.json').read_bytes())
        self.assertEqual(contract['files']['.github/workflows/kernel-lean.yml'], hashlib.sha256(KERNEL.encode()).hexdigest())
        self.assertEqual(contract['files']['scripts/test_kernel_cache.py'], hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
        self.assertIn('python -B scripts/test_kernel_cache.py', KERNEL)


if __name__ == '__main__':
    unittest.main()
