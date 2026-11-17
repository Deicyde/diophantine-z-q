import os
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

import kernel_build_environment as env


class EnvironmentTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.prefix = self.root/'toolchain'
        for directory in ('bin', 'include', 'lib/lean', 'share'):
            (self.prefix/directory).mkdir(parents=True)
        for path in ('bin/lean', 'bin/lake', 'lib/lean/Init.olean', 'include/lean.h', 'share/config'):
            (self.prefix/path).write_bytes(path.encode())

    def test_contents_permissions_and_added_files_change_identity(self):
        before = env.toolchain_inputs(self.prefix)
        self.assertIn('Init', before['builtins'])
        (self.prefix/'lib/lean/Init.olean').write_bytes(b'a poisoned object with unchanged compiler version')
        self.assertNotEqual(before['summary'], env.toolchain_inputs(self.prefix)['summary'])
        (self.prefix/'lib/lean/Init.olean').write_bytes(b'lib/lean/Init.olean')
        (self.prefix/'bin/plugin').write_bytes(b'new dynamic tool')
        self.assertNotEqual(before['summary'], env.toolchain_inputs(self.prefix)['summary'])

    def test_equal_installations_can_match_at_different_absolute_paths(self):
        copied = self.root/'other'
        shutil.copytree(self.prefix, copied)
        self.assertEqual(env.toolchain_inputs(self.prefix)['summary'], env.toolchain_inputs(copied)['summary'])

    def test_windows_executable_path_mode_does_not_mismatch_open_file_identity(self):
        executable = self.prefix/'bin/lean.exe'
        executable.write_bytes(b'Executable-shaped fixture, never executed')
        row = env.file_fingerprint(self.prefix.resolve(), executable)
        self.assertEqual(row['size'], executable.stat().st_size)

    def test_untracked_dependency_output_is_not_authenticated_by_git_revision(self):
        dep = self.root/'dependency'
        (dep/'.git').mkdir(parents=True)
        (dep/'.git/noise').write_text('not a build input')
        (dep/'.lake/build/lib/lean').mkdir(parents=True)
        (dep/'Dep.lean').write_text('theorem dep : True := True.intro')
        obj = dep/'.lake/build/lib/lean/Dep.olean'; obj.write_bytes(b'original')
        packages = {'packages': {'dep': {'type': 'git', 'revision': 'a'*40, 'location': 'dependency'}}}
        first, _ = env.dependency_inputs(self.root, packages)
        (dep/'.git/noise').write_text('metadata changed')
        self.assertEqual(first, env.dependency_inputs(self.root, packages)[0])
        obj.write_bytes(b'poisoned')
        self.assertNotEqual(first, env.dependency_inputs(self.root, packages)[0])
        (dep/'Untracked.lean').write_text('axiom surprise : False')
        files = env.dependency_inputs(self.root, packages)[1]['dep']
        self.assertIn('Untracked.lean', files)

    def test_aliases_and_overlapping_roots_are_rejected(self):
        with self.assertRaisesRegex(ValueError, 'aliased'):
            env.fingerprint_tree(self.prefix, ['.', 'lib'])
        with self.assertRaisesRegex(ValueError, 'Missing fingerprint'):
            env.fingerprint_tree(self.prefix, ['absent'])
        with self.assertRaisesRegex(ValueError, 'Unsafe fingerprint'):
            env.fingerprint_tree(self.prefix, ['../toolchain'])

    def test_external_links_are_rejected_internal_file_links_are_bound(self):
        link = self.prefix/'bin/linked'
        try:
            link.symlink_to(self.prefix/'bin/lean')
        except OSError:
            self.skipTest('Host cannot create file symlinks')
        _, files = env.fingerprint_tree(self.prefix)
        self.assertEqual(files['bin/linked']['link_target'], 'bin/lean')
        link.unlink()
        outside = self.root/'outside'; outside.write_text('outside input')
        link.symlink_to(outside)
        with self.assertRaisesRegex(ValueError, 'outside'):
            env.fingerprint_tree(self.prefix)

    def test_limits_and_changed_input_fail_closed(self):
        with patch.object(env, 'MAX_INPUT_FILES', 1):
            with self.assertRaisesRegex(ValueError, 'file limit'):
                env.fingerprint_tree(self.prefix)
        with patch.object(env, 'MAX_INPUT_BYTES', 1):
            with self.assertRaisesRegex(ValueError, 'byte limit'):
                env.fingerprint_tree(self.prefix)
        original = env.hashlib.file_digest
        def mutate(stream, algorithm):
            result = original(stream, algorithm)
            (self.prefix/'bin/lean').write_bytes(b'changed after read')
            return result
        with patch.object(env.hashlib, 'file_digest', side_effect=mutate):
            with self.assertRaisesRegex(ValueError, 'changed'):
                env.file_fingerprint(self.prefix.resolve(), self.prefix/'bin/lean')

    def test_unreadable_subdirectory_is_not_silently_omitted(self):
        def inaccessible(*args, **kwargs):
            kwargs['onerror'](PermissionError('unreadable fixture'))
        with patch.object(env.os, 'walk', side_effect=inaccessible):
            with self.assertRaisesRegex(ValueError, 'completely enumerated'):
                env.fingerprint_tree(self.prefix)

    def test_settings_and_driver_bytes_are_part_of_the_compact_identity(self):
        project = self.root/'project'; project.mkdir()
        (project/'driver.py').write_text('print(1)')
        packages = {'configuration': {}, 'packages': {}}
        args = (project, self.prefix, [['lake', 'build', 'Project']], {'Project': 'Project.lean'})
        with patch.object(env, 'package_environment', return_value=packages):
            first, _ = env.collect_environment(*args, driver_paths=['driver.py'], environ={})
            second, _ = env.collect_environment(*args, driver_paths=['driver.py'], environ={'LEAN_OPTS': '-t100'})
            self.assertNotEqual(first, second)
            (project/'driver.py').write_text('print(2)')
            self.assertNotEqual(first, env.collect_environment(*args, driver_paths=['driver.py'], environ={})[0])

    def test_verified_controls_are_portable_without_erasing_effective_settings(self):
        from kernel_build_controls import prepare_controls
        project = self.root/'project'; project.mkdir()
        (project/'driver.py').write_text('print(1)')
        args = (project, self.prefix, [['lake', 'build', 'Project']], {'Project': 'Project.lean'})
        first_dir, second_dir = self.root/'controls-a', self.root/'controls-b'
        first_env, _ = prepare_controls(project, first_dir, environ={})
        second_env, _ = prepare_controls(project, second_dir, environ={})
        with patch.object(env, 'package_environment', return_value={'configuration': {}, 'packages': {}}):
            first, _ = env.collect_environment(*args, driver_paths=['driver.py'],
                                               environ=first_env, controls=first_dir)
            second, _ = env.collect_environment(*args, driver_paths=['driver.py'],
                                                environ=second_env, controls=second_dir)
            self.assertEqual(first, second)
            second_env['LAKE_ARTIFACT_CACHE'] = 'true'
            with self.assertRaisesRegex(ValueError, 'cache controls'):
                env.collect_environment(*args, driver_paths=['driver.py'],
                                         environ=second_env, controls=second_dir)


if __name__ == '__main__':
    unittest.main()
