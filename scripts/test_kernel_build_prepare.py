import io
import unittest
from unittest.mock import patch

import kernel_build_prepare as prepare


class PreparationTests(unittest.TestCase):
    def setUp(self):
        process = patch.dict(prepare.os.environ, {}, clear=True)
        process.start()
        self.addCleanup(process.stop)
        self.archive = io.BytesIO(b'synthetic unit fixture, not a real bundle')
        self.selection = {'status': 'selected', 'producer': {'head_sha': 'a'*40},
                          'archive_sha256': 'b'*64}
        self.manifest = {'environment': {'synthetic': 'unit fixture'}}
        self.context = {'environment': self.manifest['environment'], 'modules': {'A': 'fixture'}}
        self.detail = {'synthetic': 'capture evidence'}
        self.calls = []
        def verified(*args):
            self.calls.append('verify')
            return self.manifest
        def captured(*args, **kwargs):
            self.calls.append('capture')
            self.assertEqual(kwargs['expected_environment'], self.manifest['environment'])
            return self.context, self.detail
        def installed(*args):
            self.calls.append('install')
            self.assertIs(args[0], self.archive)
            self.assertEqual(args[3], self.context['modules'])
            self.assertEqual(args[4], self.context['environment'])
            return {'status': 'restored', 'modules': ['A']}
        for name, effect in [('verify_archive', verified), ('capture_context', captured), ('install', installed)]:
            patcher = patch.object(prepare, name, side_effect=effect)
            setattr(self, name, patcher.start())
            self.addCleanup(patcher.stop)

    def run_prepare(self, **kwargs):
        args = dict(selection=self.selection, archive=self.archive, driver_paths=['check_kernel.py'],
            system_drivers=['/bin/bash'], controls='controls', environ={})
        args.update(kwargs)
        return prepare.prepare_candidate('workspace', 'toolchain', {'A': 'A.lean'},
            [['python', 'check_kernel.py']], **args)

    def test_valid_receipt_is_verified_before_configuration_then_restores_same_open_archive(self):
        result, context, detail = self.run_prepare()
        self.assertEqual(self.calls, ['verify', 'capture', 'install'])
        self.assertEqual(result['status'], 'restored')
        self.assertTrue(result['audit_required'])
        self.assertEqual(context, self.context)
        self.assertEqual(detail, self.detail)

    def test_missing_producer_does_not_query_or_restore(self):
        result, context, detail = self.run_prepare(selection={'status': 'cold'}, archive=None)
        self.assertEqual(result['status'], 'cold')
        self.assertTrue(result['audit_required'])
        self.assertEqual(self.calls, [])
        self.assertIsNone(context)
        self.assertIsNone(detail)

    def test_invalid_bundle_never_evaluates_dependency_configuration(self):
        self.verify_archive.side_effect = ValueError('poisoned bytes')
        result, _, _ = self.run_prepare()
        self.assertEqual(result['status'], 'cold')
        self.capture_context.assert_not_called()
        self.install.assert_not_called()

    def test_changed_compiler_dependencies_runtime_or_lookup_select_cold_before_install(self):
        self.capture_context.side_effect = ValueError('incompatible inputs')
        result, _, _ = self.run_prepare()
        self.assertEqual(result['status'], 'cold')
        self.assertTrue(result['audit_required'])
        self.install.assert_not_called()

    def test_restore_error_is_not_hidden_as_a_cold_build(self):
        self.install.side_effect = OSError('rollback or write failure')
        with self.assertRaisesRegex(OSError, 'rollback or write'):
            self.run_prepare()

    def test_parent_or_child_credentials_stop_before_reading_bundle(self):
        for parent in (True, False):
            with self.subTest(parent=parent):
                with patch.dict(prepare.os.environ, {'GH_TOKEN': 'fixture'} if parent else {}):
                    with self.assertRaisesRegex(ValueError, 'without credentials'):
                        self.run_prepare(environ={} if parent else {'GH_TOKEN': 'fixture'})
        self.verify_archive.assert_not_called()


if __name__ == '__main__':
    unittest.main()
