"""Regressions for project-cache provenance in the pinned kernel workflow."""
import ast
import hashlib
import json
import re
import unittest
from unittest.mock import Mock
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HEAD = 'a' * 40
KERNEL = (ROOT / '.github/workflows/kernel-lean.yml').read_text(encoding='utf-8')
STEPS = re.split(r'^      - name: ', KERNEL, flags=re.M)[1:]
RESTORES = [step for step in STEPS if re.search(r'uses: actions/cache(?:/restore)?@', step)]


def condition(step, ref, outcome='skipped', full_build=''):
    expression = re.search(r'^        if: (.*)$', step, re.M).group(1)
    for name, value in [('github.ref', ref), ('steps.scope.outcome', outcome),
                        ('steps.scope.outputs.full_build', full_build)]:
        expression = expression.replace(name, repr(value))
    expression = expression.replace('&&', ' and ').replace('||', ' or ')
    tree = ast.parse(expression, mode='eval')
    allowed = (ast.Expression, ast.BoolOp, ast.And, ast.Or, ast.Compare,
               ast.Eq, ast.NotEq, ast.Constant)
    if any(not isinstance(node, allowed) for node in ast.walk(tree)):
        raise AssertionError('Unhandled cache condition syntax')
    return eval(compile(tree, '<cache-step-condition>', 'eval'), {'__builtins__': {}})


class KernelCacheTests(unittest.TestCase):
    def test_all_project_cache_restores_are_main_only(self):
        self.assertEqual(len(RESTORES), 1)
        self.assertIn('path: .lake/build', RESTORES[0])
        self.assertIn("github.ref == 'refs/heads/main' && (", RESTORES[0])
        # Test the actual expression's precedence, including both fail-open
        # scope cases which must NOT make a non-main restore eligible.
        refs = ['refs/heads/contributor-branch', 'refs/pull/133/merge',
                'refs/tags/main', 'refs/heads/main-other',
                'refs/heads/codex/protocol-b-kernel/133/' + HEAD + '/' + 'b'*40]
        for ref in refs:
            for outcome, full in [('skipped', ''), ('failure', ''),
                                  ('success', 'true'), ('success', 'false')]:
                with self.subTest(ref=ref, outcome=outcome, full=full):
                    self.assertFalse(condition(RESTORES[0], ref, outcome, full))

    def test_preexisting_branch_cache_is_never_queried(self):
        # A prior run may have saved either an exact or fallback match in the
        # predictable branch namespace. Do not rely on that namespace being new.
        refs = ['refs/heads/contributor-branch',
                'refs/heads/codex/protocol-b-kernel/133/' + HEAD + '/' + 'b'*40]
        for ref in refs:
            for match in ['exact-key', 'fallback-key']:
                restore = Mock(return_value={'existing_match': match, 'ref': ref})
                for step in RESTORES:
                    if condition(step, ref):
                        restore(step)
                with self.subTest(ref=ref, match=match):
                    restore.assert_not_called()

    def test_main_restore_and_scope_skip_are_preserved(self):
        self.assertTrue(condition(RESTORES[0], 'refs/heads/main'))
        self.assertTrue(condition(RESTORES[0], 'refs/heads/main', 'success', 'true'))
        self.assertFalse(condition(RESTORES[0], 'refs/heads/main', 'success', 'false'))

    def test_contract_pins_this_workflow_and_this_test(self):
        digest = hashlib.sha256(KERNEL.encode()).hexdigest()
        contract = json.loads((ROOT / 'KERNEL_CONTRACT.json').read_bytes())
        self.assertEqual(contract['files']['.github/workflows/kernel-lean.yml'], digest)
        self.assertEqual(contract['files']['scripts/test_kernel_cache.py'],
                         hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
        self.assertIn('python -B scripts/test_kernel_cache.py', KERNEL)


if __name__ == '__main__':
    unittest.main()
