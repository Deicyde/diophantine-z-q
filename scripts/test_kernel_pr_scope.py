"""Offline tests of the first-step kernel classifier; no Lean or network."""
import base64
import copy
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import kernel_pr_scope as scope

ROOT = Path(__file__).resolve().parents[1]
BASE, HEAD = 'a' * 40, 'b' * 40


class ScopeTests(unittest.TestCase):
    def setUp(self):
        self.rows = [{'filename': 'docs/guide.md', 'status': 'modified'}]
        self.current = {'number': 1, 'base': {'sha': BASE}, 'head': {'sha': HEAD}, 'changed_files': 1}
        self.event = {'pull_request': copy.deepcopy(self.current)}
        self.locked = {'ZInQKernel.lean'}

    def api(self, repo, path):
        if path == '/pulls/1':
            return copy.deepcopy(self.current)
        if path.startswith('/pulls/1/files?'):
            page = int(path.split('page=')[-1])
            return self.rows[(page - 1) * 100:page * 100]
        if path.startswith('/contents/KERNEL_CONTRACT.json?ref='):
            value = {'schema': 'kernel-contract/v1', 'files': {p: 'c' * 64 for p in self.locked}}
            return {'type': 'file', 'encoding': 'base64', 'content': base64.b64encode(json.dumps(value).encode()).decode()}
        raise AssertionError(path)

    def decide(self):
        with patch.object(scope, 'api', side_effect=self.api):
            return scope.decide('pull_request', self.event, 'x/y')

    def test_docs_only_skip_and_kernel_source_build(self):
        full, reason, paths = self.decide()
        self.assertFalse(full)
        self.assertEqual(paths, ['docs/guide.md'])
        self.rows[0]['filename'] = 'ZInQKernel/Contrib/Proof.lean'
        self.assertTrue(self.decide()[0])

    def test_push_and_manual_always_build(self):
        with patch.object(scope, 'api') as api:
            for event in ['push', 'workflow_dispatch', 'unknown']:
                self.assertTrue(scope.decide(event, {}, 'x/y')[0])
            api.assert_not_called()

    def test_all_current_contract_files_force_build(self):
        locked = set(json.loads((ROOT / 'KERNEL_CONTRACT.json').read_text())['files'])
        for path in locked:
            self.assertTrue(scope.affects_kernel(path, locked), path)

    def test_additional_and_future_inputs_force_build(self):
        paths = ['ThirdParty/GreenTao/Submission.lean', 'ThirdParty/Other/data.csv',
                 'research/archive/Old.lean', 'other/lakefile.lean', 'other/lakefile.toml',
                 'lean/Frozen/BoundedIntegerPolynomial.lean', 'scripts/audit_kernel.lean',
                 'scripts/check_target.py', 'scripts/new_kernel_test.py', 'scripts/new_helper.py',
                 'tests/new_fixture.json', 'build/kernel-ci/base-audit.json', '.gitattributes',
                 '.gitmodules', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
                 'KERNEL_CONTRACT.json', '.github/workflows/kernel-lean.yml', 'unknown.dat']
        for path in paths:
            self.assertTrue(scope.affects_kernel(path, set()), path)

    def test_independent_gate_and_document_formats_skip(self):
        for path in ['README.md', 'CREDITS.md', 'paper/current.tex', 'paper/current.pdf',
                     'docs/refs.bib', '.github/workflows/protocol-b.yml',
                     '.github/protocol-b-reviewer.md', 'tests/protocol_b/test_gate.py']:
            self.assertFalse(scope.affects_kernel(path, set()), path)

    def test_pinned_document_still_builds(self):
        self.locked.add('docs/guide.md')
        self.assertTrue(self.decide()[0])

    def test_both_rename_paths_are_checked(self):
        self.rows = [{'filename': 'docs/former-source.md', 'previous_filename': 'Old.lean', 'status': 'renamed'}]
        self.assertTrue(self.decide()[0])

    def test_pagination_reaches_later_kernel_change(self):
        self.rows = [{'filename': f'docs/{i}.md', 'status': 'modified'} for i in range(201)]
        self.rows[-1]['filename'] = 'ZInQKernel/Last.lean'
        self.current['changed_files'] = len(self.rows)
        self.assertTrue(self.decide()[0])

    def test_incomplete_duplicate_or_large_list_is_ambiguous(self):
        self.current['changed_files'] = 2
        with self.assertRaises(ValueError):
            self.decide()
        self.rows *= 2
        with self.assertRaises(ValueError):
            self.decide()
        self.current['changed_files'] = 3001
        with self.assertRaises(ValueError):
            self.decide()

    def test_head_race_and_malformed_row_are_ambiguous(self):
        self.current['head']['sha'] = 'd' * 40
        with self.assertRaises(ValueError):
            self.decide()
        self.current['head']['sha'] = HEAD
        self.rows[0]['status'] = 'renamed'
        with self.assertRaises(KeyError):
            self.decide()

    def test_failure_writes_full_build_and_skip_writes_summary(self):
        for failed in [False, True]:
            with tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                (root / 'event.json').write_text(json.dumps(self.event))
                env = {'GITHUB_EVENT_NAME': 'pull_request', 'GITHUB_EVENT_PATH': str(root / 'event.json'),
                       'GITHUB_REPOSITORY': 'x/y', 'GITHUB_OUTPUT': str(root / 'output'),
                       'GITHUB_STEP_SUMMARY': str(root / 'summary')}
                with patch.dict(os.environ, env), patch.object(scope, 'api', side_effect=OSError('offline') if failed else self.api):
                    scope.main()
                self.assertEqual((root / 'output').read_text(), 'full_build=' + str(failed).lower() + '\n')
                self.assertIn('performing the full build' if failed else 'Kernel build skipped', (root / 'summary').read_text())

    def test_workflow_embeds_exact_classifier_and_keeps_required_job(self):
        workflow = (ROOT / '.github/workflows/kernel-lean.yml').read_text()
        block = workflow.split('          # BEGIN KERNEL SCOPE\n')[1].split('          # END KERNEL SCOPE\n')[0]
        embedded = '\n'.join(line[10:] for line in block.splitlines()) + '\n'
        self.assertEqual(embedded, (ROOT / 'scripts/kernel_pr_scope.py').read_text())
        compile(embedded, '<kernel first step>', 'exec')
        self.assertIn('name: Complete kernel build and exact-target audit', workflow)
        self.assertNotIn('paths:', workflow)
        self.assertNotIn('paths-ignore:', workflow)
        self.assertNotIn("protected controller", workflow)
        steps = workflow.split('      - name: ')[1:]
        self.assertIn('id: scope', steps[0])
        self.assertIn('continue-on-error: true', steps[0])
        self.assertIn("if: github.event_name == 'pull_request'", steps[0])
        for step in steps[1:]:
            self.assertIn("steps.scope.outcome != 'success' || steps.scope.outputs.full_build != 'false'", step)


if __name__ == '__main__':
    unittest.main()
