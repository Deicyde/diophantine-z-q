import copy
import json
import subprocess
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import kernel_build_driver as driver


class DriverTests(unittest.TestCase):
    def setUp(self):
        environment = patch.dict(driver.os.environ, {}, clear=True)
        environment.start(); self.addCleanup(environment.stop)
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.workspace, self.state = self.root/'workspace', self.root/'state'
        self.workspace.mkdir(); self.state.mkdir()
        self.context = {'schema': 'kernel-build-context/v1', 'environment': {'test': 'unit fixture'},
            'modules': {'A': {'inputs': {'source_path': 'A.lean', 'source_sha256': 'a'*64,
                'project_imports': [], 'header': {'isModule': False, 'imports': []}}}},
            'project_paths': {'A': {'source_path': 'A.lean', 'lean_output_prefix': '.lake/build/lib/lean/A',
                                  'ir_output_prefix': '.lake/build/ir/A'}}}
        self.producer = {'repository': 'owner/repo', 'head_sha': 'a'*40, 'run_id': 123, 'run_attempt': 1,
            'workflow_sha256': 'b'*64, 'event': 'push', 'ref': 'refs/heads/main'}

    def cold(self):
        driver.write_new(self.state/'selection.json', {'status': 'cold'})

    def fixture_outputs(self):
        for path in ['.lake/build/lib/lean/A.'+x for x in ('olean', 'ilean', 'trace')] + [
                '.lake/build/ir/A.c', '.lake/build/ir/A.setup.json']:
            file = self.workspace/path
            file.parent.mkdir(parents=True, exist_ok=True)
            file.write_text('synthetic unit fixture '+path)
        ci = self.workspace/'build/kernel-ci'
        ci.mkdir(parents=True)
        identity = {'head_sha': 'a'*40, 'contract_sha256': 'c'*64, 'compiler': 'unit fixture', 'modules': ['A']}
        driver.write_new(ci/'build-complete.json', {'schema': 'kernel-build-complete/v1', 'status': 'complete', 'identity': identity})
        driver.write_new(ci/'audit.json', {'schema': 'kernel-audit/v1', 'status': 'passed', **identity})

    def test_capture_saves_changed_file_evidence_and_still_refuses(self):
        previous = {'installed_inputs': {'dependency_files': {'dep': {
            'Dep.olean': {'sha256': 'a'*64, 'size': 4}}}}}
        driver.write_new(self.state/'inputs-before.json', previous)
        error = driver.InputContextMismatch('Installed build inputs differ',
            {'dependency_inputs': 'old'}, {'dependency_inputs': 'new'},
            {'dependency_files': {'dep': {'Dep.olean': {'sha256': 'b'*64, 'size': 4}}}})
        with patch.object(driver, 'validate', return_value={'modules': {}}), \
                patch.object(driver, 'capture_context', side_effect=error):
            with self.assertRaisesRegex(driver.InputContextMismatch, 'Installed build inputs differ'):
                driver.capture(self.workspace, self.root/'prefix', self.state, expected={})
        evidence = driver.read(self.state/'input-mismatch.json')
        self.assertEqual(evidence['changed_file_counts'], {'dependency/dep': 1})
        self.assertEqual(evidence['file_examples'][0]['path'], 'Dep.olean')
        self.assertFalse(evidence['acceptance'])
        self.assertEqual(driver.read(self.state/'inputs-before.json'), previous)
        self.assertFalse((self.state/'session-built.json').exists())
        self.assertFalse((self.state/'bundle').exists())

    def test_cold_pr_does_not_capture_or_publish_and_preserves_controls(self):
        self.cold()
        with patch.object(driver, 'capture') as capture:
            result = driver.prepare(self.workspace, self.state, self.root/'toolchain')
            self.assertEqual(result['status'], 'cold')
            self.assertTrue(result['audit_required'])
            capture.assert_not_called()
        self.assertFalse(driver.completed_phase(self.workspace, self.state, 'built')['publish'])
        self.assertFalse(driver.completed_phase(self.workspace, self.state, 'finish')['publish'])
        self.assertFalse((self.state/'bundle').exists())

    def test_main_input_query_timeout_keeps_cold_build_and_audit_available(self):
        self.cold()
        with patch.object(driver, 'producer_identity', return_value=self.producer), \
                patch.object(driver, 'capture', side_effect=subprocess.TimeoutExpired(['lake', 'env'], 60)):
            result = driver.prepare(self.workspace, self.state, self.root/'toolchain')
        self.assertEqual(result['status'], 'cold')
        self.assertEqual(result['producer_unavailable'], 'TimeoutExpired')
        self.assertTrue(result['audit_required'])
        config = driver.read(self.state/'prepared.json')
        self.assertFalse(config['has_context'])
        self.assertFalse(driver.completed_phase(self.workspace, self.state, 'built')['publish'])
        self.assertFalse(driver.completed_phase(self.workspace, self.state, 'finish')['publish'])
        self.assertFalse((self.state/'bundle').exists())

    def test_main_sequence_requires_unchanged_capture_and_actual_complete_reports(self):
        self.cold()
        with patch.object(driver, 'producer_identity', return_value=self.producer), \
                patch.object(driver, 'capture', side_effect=lambda *a, **k: (copy.deepcopy(self.context), {})):
            driver.prepare(self.workspace, self.state, self.root/'toolchain')
            self.fixture_outputs()
            driver.completed_phase(self.workspace, self.state, 'built')
            result = driver.completed_phase(self.workspace, self.state, 'finish')
        self.assertTrue(result['publish'])
        self.assertEqual(result['staged']['files'], 5)
        self.assertTrue((self.state/'bundle/manifest.json').exists())

    def test_cache_metadata_preparation_is_requested_only_before_the_initial_baseline(self):
        self.cold()
        with patch.object(driver, 'producer_identity', return_value=self.producer), \
                patch.object(driver, 'capture', side_effect=lambda *a, **k: (copy.deepcopy(self.context), {})) as capture:
            driver.prepare(self.workspace, self.state, self.root/'toolchain')
            self.fixture_outputs()
            driver.completed_phase(self.workspace, self.state, 'built')
            driver.completed_phase(self.workspace, self.state, 'finish')
        self.assertEqual([c.kwargs.get('prepare_cache_metadata', False) for c in capture.call_args_list],
                         [True, False, False])

    def test_initial_metadata_changes_are_preserved_as_diagnostics_not_a_replacement_baseline(self):
        self.cold()
        record = {'schema': 'kernel-cache-metadata/v1', 'changes': [{'path': 'fixture.hash'}]}
        with patch.object(driver, 'producer_identity', return_value=self.producer), \
                patch.object(driver, 'capture', return_value=(copy.deepcopy(self.context), {'metadata_preparation': record})):
            driver.prepare(self.workspace, self.state, self.root/'toolchain')
        self.assertEqual(driver.read(self.state/'metadata-preparation.json'), record)
        self.assertEqual(driver.read(self.state/'session-prepared.json')['context'], self.context)

    def test_changed_build_inputs_prevent_built_state_and_publication(self):
        self.cold()
        with patch.object(driver, 'producer_identity', return_value=self.producer), \
                patch.object(driver, 'capture', side_effect=lambda *a, **k: (copy.deepcopy(self.context), {})):
            driver.prepare(self.workspace, self.state, self.root/'toolchain')
            self.fixture_outputs()
            self.context['environment']['changed'] = True
            with self.assertRaisesRegex(ValueError, 'Inputs changed during the build'):
                driver.completed_phase(self.workspace, self.state, 'built')
        self.assertFalse((self.state/'session-built.json').exists())
        self.assertFalse((self.state/'bundle').exists())

    def test_missing_or_failed_audit_does_not_publish(self):
        self.cold()
        with patch.object(driver, 'producer_identity', return_value=self.producer), \
                patch.object(driver, 'capture', side_effect=lambda *a, **k: (copy.deepcopy(self.context), {})):
            driver.prepare(self.workspace, self.state, self.root/'toolchain')
            self.fixture_outputs()
            driver.completed_phase(self.workspace, self.state, 'built')
            audit = self.workspace/'build/kernel-ci/audit.json'
            data = json.loads(audit.read_text()); data['status'] = 'failed'
            audit.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, 'successful full audit'):
                driver.completed_phase(self.workspace, self.state, 'finish')
        self.assertFalse((self.state/'bundle').exists())

    def test_non_main_refs_and_events_cannot_claim_producer_authority(self):
        for ref, event in [('refs/heads/Main', 'push'), ('refs/pull/1/merge', 'pull_request'),
                           ('refs/heads/codex/protocol-b-kernel/1', 'workflow_dispatch'),
                           ('refs/heads/main', 'pull_request')]:
            self.assertIsNone(driver.producer_identity(self.workspace, {'GITHUB_REF': ref, 'GITHUB_EVENT_NAME': event}))

    def test_main_identity_requires_actual_checkout_and_run(self):
        workflow = self.workspace/driver.WORKFLOW
        workflow.parent.mkdir(parents=True); workflow.write_text('unit fixture')
        environment = {'GITHUB_REF': 'refs/heads/main', 'GITHUB_EVENT_NAME': 'workflow_dispatch',
            'GITHUB_REPOSITORY': 'owner/repo', 'GITHUB_SHA': 'a'*40, 'GITHUB_RUN_ID': '123', 'GITHUB_RUN_ATTEMPT': '2'}
        with patch.object(driver, 'git', return_value=('a'*40).encode()):
            result = driver.producer_identity(self.workspace, environment)
        self.assertEqual(result['run_attempt'], 2)
        with patch.object(driver, 'git', return_value=('b'*40).encode()):
            with self.assertRaisesRegex(ValueError, 'not the main run commit'):
                driver.producer_identity(self.workspace, environment)

    def test_state_cannot_be_replayed_or_put_in_the_candidate_checkout(self):
        self.cold()
        driver.prepare(self.workspace, self.state, self.root/'toolchain')
        with self.assertRaisesRegex(ValueError, 'do not replay'):
            driver.prepare(self.workspace, self.state, self.root/'toolchain')
        nested = self.workspace/'state'; nested.mkdir()
        with self.assertRaisesRegex(ValueError, 'outside the candidate'):
            driver.checked_state(self.workspace, nested)


if __name__ == '__main__':
    unittest.main()
