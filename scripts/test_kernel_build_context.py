import copy
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import kernel_build_context as context


class ContextTests(unittest.TestCase):
    def setUp(self):
        clean_process = patch.dict(context.os.environ, {}, clear=True)
        clean_process.start()
        self.addCleanup(clean_process.stop)
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.workspace, self.prefix = self.root/'workspace', self.root/'toolchain'
        self.workspace.mkdir(); self.prefix.mkdir()
        self.identity = {'packages': {'packages': {}}, 'toolchain': {'sha256': 'a'*64},
                         'dependency_inputs': {}, 'source_resolution': {'libraries': ['Fixture']}}
        self.detail = {'toolchain_files': {'bin/lean': {'sha256': 'b'*64}},
                       'builtins': {}, 'dependency_files': {}}
        self.binding = {'project_layout': {'libraries': ['Fixture']},
                        'project_resolution': {'Fixture': {'source_path': 'Fixture.lean'}}}
        self.modules = {'Fixture': {'inputs': {'source_sha256': 'c'*64}}}
        self.lookup = {'LEAN': str(self.prefix/'bin/lean'), 'LEAN_PATH': str(self.workspace/'.lake/build')}
        self.runtime = {'schema': 'kernel-linux-runtime/v1', 'sha256': 'd'*64}
        for name, value in [('verify_controls', {}), ('project_layout', self.binding['project_layout']),
                ('collect_environment', (self.identity, self.detail)),
                ('capture_lake_environment', self.lookup),
                ('collect_bound_inventory', (self.modules, self.binding)),
                ('capture_runtime', (self.runtime, {'files': {}}))]:
            mocked = patch.object(context, name, side_effect=lambda *a, _v=value, **kw: copy.deepcopy(_v)).start()
            self.addCleanup(patch.stopall)
            setattr(self, name, mocked)
        patch.object(context.platform, 'system', return_value='Linux').start()

    def capture(self, **kwargs):
        return context.capture_context(self.workspace, self.prefix, {'Fixture': 'Fixture.lean'},
            [['python', 'check_kernel.py', '--phase', 'build']], driver_paths=['check_kernel.py'],
            system_drivers=['/usr/bin/python3', '/usr/bin/git', '/bin/bash'],
            controls=self.root/'controls', environ={}, **kwargs)

    def test_mismatching_installed_inputs_stop_before_dependency_configuration_executes(self):
        with self.assertRaisesRegex(ValueError, 'Installed build inputs differ'):
            self.capture(expected_environment={**self.identity, 'toolchain': {'sha256': 'e'*64}})
        self.capture_lake_environment.assert_not_called()
        self.capture_runtime.assert_not_called()

    def test_complete_capture_binds_actual_lookup_runtime_and_module_inputs(self):
        first, detail = self.capture()
        self.assertEqual(first['environment']['runtime'], self.runtime)
        self.assertEqual(first['environment']['actual_lookup']['LEAN'], '@toolchain/bin/lean')
        self.assertEqual(first['modules'], self.modules)
        self.assertEqual(detail['actual_lookup'], self.lookup)
        again, _ = self.capture(expected_environment=first['environment'])
        self.assertEqual(first, again)

    def test_changed_runtime_or_lookup_does_not_authorize_restoration(self):
        first, _ = self.capture()
        expected = first['environment']
        for field in ('runtime', 'actual_lookup'):
            changed = copy.deepcopy(expected)
            changed[field] = {'unexpected': 'different effective input'}
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'lookup or runtime differs'):
                self.capture(expected_environment=changed)

    def test_changed_layout_during_queries_is_rejected(self):
        self.binding['project_layout'] = {'libraries': ['Different']}
        with self.assertRaisesRegex(ValueError, 'layout changed'):
            self.capture()
        self.capture_runtime.assert_not_called()

    def test_extra_independent_module_does_not_change_common_environment(self):
        first, _ = self.capture()
        self.modules['Fixture.Other'] = {'inputs': {'source_sha256': 'e'*64}}
        self.binding['project_resolution']['Fixture.Other'] = {'source_path': 'Fixture/Other.lean'}
        second, _ = self.capture(expected_environment=first['environment'])
        self.assertEqual(first['environment'], second['environment'])
        self.assertNotEqual(first['modules'], second['modules'])

    def test_credentials_or_unsupported_platform_stop_before_fingerprinting(self):
        with patch.object(context.platform, 'system', return_value='Windows'):
            with self.assertRaisesRegex(ValueError, 'requires Linux'):
                self.capture()
        with self.assertRaisesRegex(ValueError, 'credential-free'):
            context.capture_context(self.workspace, self.prefix, {}, [], driver_paths=[],
                system_drivers=[], controls=self.root/'controls', environ={'GH_TOKEN': 'fixture'})
        self.collect_environment.assert_not_called()

    def test_portable_lookup_preserves_external_and_relative_search_entries(self):
        result = context.portable_lookup(self.workspace, self.prefix, {
            'LEAN': str(self.prefix/'bin/lean'), 'LEAN_PATH': '../shadow', 'LAKE': '/external/lake'})
        self.assertEqual(result['LEAN'], '@toolchain/bin/lean')
        self.assertEqual(result['LEAN_PATH'], ['../shadow'])
        self.assertEqual(result['LAKE'], '/external/lake')

    def test_clean_child_environment_cannot_hide_parent_credentials(self):
        with patch.dict(context.os.environ, {'GH_TOKEN': 'fixture-only'}):
            with self.assertRaisesRegex(ValueError, 'credential-free'):
                self.capture()
        self.collect_environment.assert_not_called()
        self.capture_lake_environment.assert_not_called()


if __name__ == '__main__':
    unittest.main()
