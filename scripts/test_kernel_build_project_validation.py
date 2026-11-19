import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import validate_kernel_reuse_project as project
from kernel_build_manifest import validate_manifest


class ProjectValidationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.workspace = self.root/'project'
        self.workspace.mkdir()
        (self.workspace/'build').mkdir()
        self.state = self.root/'state'
        self.output = self.workspace/'build/evidence'
        environment = patch.dict(os.environ, {}, clear=True)
        environment.start(); self.addCleanup(environment.stop)

    def test_credentials_rejected_before_state_or_candidate_execution(self):
        for key in project.FORBIDDEN_ENV:
            with self.subTest(key=key), patch.object(project.sys, 'platform', 'linux'), \
                    patch.dict(os.environ, {key: 'test-only'}), patch.object(project.driver, 'prepare') as prepare:
                with self.assertRaisesRegex(ValueError, 'No credentials'):
                    project.validate(self.workspace, self.state, self.output, self.root)
                prepare.assert_not_called()
                self.assertFalse(self.state.exists())

    def test_live_workflow_output_paths_are_rejected(self):
        for key in ('GITHUB_ENV', 'GITHUB_OUTPUT'):
            with self.subTest(key=key), patch.object(project.sys, 'platform', 'linux'), \
                    patch.dict(os.environ, {key: str(self.root/'workflow-output')}):
                with self.assertRaisesRegex(ValueError, 'must not write workflow'):
                    project.validate(self.workspace, self.state, self.output, self.root)
                self.assertFalse(self.state.exists())

    def test_non_linux_and_old_state_cannot_be_reused(self):
        with patch.object(project.sys, 'platform', 'win32'):
            with self.assertRaisesRegex(ValueError, 'must run on Linux'):
                project.validate(self.workspace, self.state, self.output, self.root)
        self.state.mkdir(); (self.state/'keep').write_text('old evidence')
        with patch.object(project.sys, 'platform', 'linux'):
            with self.assertRaisesRegex(ValueError, 'fresh validation state'):
                project.validate(self.workspace, self.state, self.output, self.root)
        self.assertEqual((self.state/'keep').read_text(), 'old evidence')

    def test_existing_project_outputs_are_not_used_for_the_cold_build(self):
        output = self.workspace/'.lake/build'
        output.mkdir(parents=True)
        (output/'keep').write_text('existing')
        with patch.object(project.sys, 'platform', 'linux'):
            with self.assertRaisesRegex(ValueError, 'absent project build outputs'):
                project.validate(self.workspace, self.state, self.output, self.root)
        self.assertEqual((output/'keep').read_text(), 'existing')
        self.assertFalse(self.state.exists())

    def test_backup_moves_only_project_outputs_and_preserves_dependency_objects(self):
        for relative in ('.lake/build', 'lean/.lake/build', '.lake/packages/dep/.lake/build'):
            path = self.workspace/relative
            path.mkdir(parents=True)
            (path/'object').write_text(relative)
        backup = self.root/'backup'
        moved = project.preserve_project_outputs(self.workspace, backup)
        self.assertEqual(moved, list(project.BUILD_ROOTS))
        self.assertEqual((backup/'0/object').read_text(), '.lake/build')
        self.assertEqual((backup/'1/object').read_text(), 'lean/.lake/build')
        self.assertEqual((self.workspace/'.lake/packages/dep/.lake/build/object').read_text(),
                         '.lake/packages/dep/.lake/build')
        for relative in project.BUILD_ROOTS:
            self.assertFalse((self.workspace/relative).exists())

    def test_early_probe_cannot_compile_or_claim_a_successful_build(self):
        self.output.mkdir()
        with patch.object(project.subprocess, 'run') as run:
            run.return_value.returncode = 1  # Missing project outputs is expected.
            result = project.probe_cached_inputs(self.workspace, self.output)
        self.assertEqual(run.call_args.args[0],
                         ['lake', '--rehash', '--no-build', 'build', 'ZInQKernel', 'GreenTaoVendor'])
        self.assertEqual(result['exit_code'], 1)
        self.assertIn('neither build nor audit acceptance', result['scope'])
        self.assertFalse((self.workspace/'build/kernel-ci/build-complete.json').exists())
        self.assertFalse((self.workspace/'build/kernel-ci/audit.json').exists())

    def test_backup_cannot_target_checkout_or_overwrite_prior_evidence(self):
        source = self.workspace/'.lake/build'
        source.mkdir(parents=True); (source/'keep').write_text('built')
        prior = self.root/'prior'; prior.mkdir()
        for backup in (self.workspace/'inside', prior):
            with self.subTest(backup=backup):
                with self.assertRaisesRegex(ValueError, 'Backup must be new and outside'):
                    project.preserve_project_outputs(self.workspace, backup)
        self.assertEqual((source/'keep').read_text(), 'built')

    def test_every_module_is_checked_without_compilation(self):
        modules = ['M'+str(i) for i in range(944)]
        commands = list(project.no_build_commands(modules))
        self.assertEqual([target[1:] for cmd in commands[1:] for target in cmd[4:]], modules)
        self.assertTrue(all(cmd[:4] == ['lake', '--rehash', '--no-build', 'build'] for cmd in commands))
        self.assertEqual(commands[0][4:], ['ZInQKernel', 'GreenTaoVendor'])

    def test_fixture_identity_cannot_equal_real_github_producer_identity(self):
        workflow = self.workspace/project.WORKFLOW
        workflow.parent.mkdir(parents=True); workflow.write_text('fixture')
        with patch.object(project.driver, 'git', return_value=b'a'*40):
            identity = project.fixture_identity(self.workspace)
        self.assertEqual(identity['scope'], project.SCOPE)
        self.assertEqual(identity['repository'], 'local-validation/not-an-authenticated-producer')
        actual_shape = {k: v for k, v in identity.items() if k != 'scope'}
        # validate_manifest compares the complete identities before reading any
        # module inventory, so the test-only field rejects even otherwise equal facts.
        with self.assertRaisesRegex(ValueError, 'Wrong bundle producer'):
            validate_manifest({'schema': 'kernel-main-build/v1', 'producer': identity}, actual_shape)

    def test_failed_capture_preserves_original_diagnostic_in_uploaded_evidence(self):
        workflow = self.workspace/project.WORKFLOW
        workflow.parent.mkdir(parents=True); workflow.write_text('fixture')
        evidence = {'schema': 'kernel-input-mismatch/v1', 'acceptance': False,
                    'decision': 'rejected', 'changed_categories': ['dependency_inputs']}
        def prepare(*args):
            project.driver.write_new(self.state/'producer/input-mismatch.json', evidence)
            raise ValueError('Installed build inputs differ')
        with patch.object(project.sys, 'platform', 'linux'), \
                patch.object(project.driver, 'git', return_value=b'a'*40), \
                patch.object(project.driver, 'prepare', side_effect=prepare), \
                patch.object(project.subprocess, 'run') as execute:
            with self.assertRaisesRegex(ValueError, 'Installed build inputs differ'):
                project.validate(self.workspace, self.state, self.output, self.root)
        execute.assert_not_called()
        self.assertEqual((self.output/'producer-input-mismatch.json').read_bytes(),
                         (self.state/'producer/input-mismatch.json').read_bytes())
        self.assertEqual(json.loads((self.output/'result.json').read_text())['status'], 'failed')

    def exercise_probe_sequence(self, *, mismatch):
        workflow = self.workspace/project.WORKFLOW
        workflow.parent.mkdir(parents=True); workflow.write_text('fixture')
        context = {'environment': {'identity': 'prepared'}, 'modules': {'A': {}}}
        def prepare(*args):
            project.driver.write_new(self.state/'producer/prepared.json', {'has_context': True})
            project.driver.write_new(self.state/'producer/session-prepared.json', {'context': context})
            return {'status': 'cold'}
        def execute(command, **kwargs):
            from types import SimpleNamespace
            return SimpleNamespace(returncode=1 if '--no-build' in command else 0)
        with patch.object(project.sys, 'platform', 'linux'), \
                patch.object(project.driver, 'git', return_value=b'a'*40), \
                patch.object(project.driver, 'prepare', side_effect=prepare), \
                patch.object(project.driver, 'validate', return_value={'modules': {'A': {}}}), \
                patch.object(project.driver, 'capture',
                             side_effect=ValueError('probe mismatch') if mismatch else None,
                             return_value=(context, {})), \
                patch.object(project.driver, 'completed_phase', side_effect=ValueError('after full build')) as completed, \
                patch.object(project.subprocess, 'run', side_effect=execute) as run:
            with self.assertRaisesRegex(ValueError, 'probe mismatch' if mismatch else 'after full build'):
                project.validate(self.workspace, self.state, self.output, self.root)
        commands = [call.args[0] for call in run.call_args_list]
        self.assertIn('--no-build', commands[0])
        if mismatch:
            self.assertEqual(len(commands), 1)
            completed.assert_not_called()
        else:
            self.assertEqual(commands[1], ['python', '-B', 'scripts/check_kernel.py', '--phase', 'build'])
            self.assertEqual(len(commands), 2)
            completed.assert_called_once()
        self.assertEqual(json.loads((self.output/'result.json').read_text())['status'], 'failed')

    def test_probe_input_mismatch_stops_before_full_project_compilation(self):
        self.exercise_probe_sequence(mismatch=True)

    def test_unchanged_probe_still_requires_full_project_compilation(self):
        self.exercise_probe_sequence(mismatch=False)

    def test_no_context_is_a_failed_dry_run_not_an_untested_cold_success(self):
        workflow = self.workspace/project.WORKFLOW
        workflow.parent.mkdir(parents=True); workflow.write_text('fixture')
        def prepare(*args):
            project.driver.write_new(self.state/'producer/prepared.json', {'has_context': False})
            return {'status': 'cold'}
        with patch.object(project.sys, 'platform', 'linux'), \
                patch.object(project.driver, 'git', return_value=b'a'*40), \
                patch.object(project.driver, 'prepare', side_effect=prepare), \
                patch.object(project.subprocess, 'run') as execute:
            with self.assertRaisesRegex(ValueError, 'input capture did not succeed'):
                project.validate(self.workspace, self.state, self.output, self.root)
        execute.assert_not_called()
        report = json.loads((self.output/'result.json').read_text())
        self.assertEqual(report['status'], 'failed')
        self.assertFalse(report['acceptance'])
        self.assertFalse(report['authenticated_reuse'])


class ProjectWorkflowTests(unittest.TestCase):
    def test_dry_run_cannot_upload_a_production_bundle_or_gain_secret_permissions(self):
        workflow = (Path(__file__).resolve().parents[1]/'.github/workflows/kernel-reuse-validation.yml').read_text()
        full = workflow.split('  full_project:', 1)[1]
        self.assertIn('permissions:\n  contents: read', workflow)
        self.assertNotIn('secrets.', workflow)
        self.assertNotIn('environment:', workflow)
        self.assertNotIn('kernel-main-build-', full)
        self.assertNotIn('actions/cache', full)
        self.assertIn('kernel-reuse-project-validation-${{ github.run_attempt }}', full)
        self.assertNotIn('path: ${{ runner.temp }}', full)
        self.assertIn('-u GITHUB_ENV -u GITHUB_OUTPUT', full)
        for key in project.FORBIDDEN_ENV:
            self.assertIn('-u '+key+' ', full)

    def test_dry_run_retains_approved_workers_memory_and_progress_evidence(self):
        workflow = (Path(__file__).resolve().parents[1]/'.github/workflows/kernel-reuse-validation.yml').read_text()
        full = workflow.split('  full_project:', 1)[1]
        self.assertIn('timeout-minutes: 360', full)
        self.assertIn("LEAN_NUM_THREADS: '2'", full)
        self.assertIn('sudo fallocate -l 24G', full)
        self.assertIn('--record-swap build/kernel-ci/swap-status.json', full)
        self.assertIn('mode: start', full)
        self.assertIn('mode: stop', full)
        self.assertIn('build/kernel-ci/', full)


if __name__ == '__main__':
    unittest.main()
