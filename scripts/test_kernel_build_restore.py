import copy
import hashlib
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import kernel_build_restore as restore
import test_kernel_build_manifest as fixture_data


class RestoreTests(unittest.TestCase):
    def setUp(self):
        self.fixture = fixture_data.ManifestTests()
        self.fixture.setUp()
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.workspace = Path(self.temp.name)
        (self.workspace / 'lean').mkdir()
        dependency = self.workspace / '.lake/packages/pinned/lib/keep.olean'
        dependency.parent.mkdir(parents=True)
        dependency.write_bytes(b'never remove or overwrite a dependency')
        self.dependency = dependency

    def install(self, *, stream=None, current=None, env=None):
        stream = stream or self.fixture.archive()
        return restore.install(stream, hashlib.sha256(stream.getvalue()).hexdigest(),
            self.fixture.producer, current or self.fixture.manifest['modules'],
            env or self.fixture.manifest['environment'], self.workspace)

    def assert_cold(self):
        self.assertFalse((self.workspace / '.lake/build').exists())
        self.assertFalse((self.workspace / 'lean/.lake/build').exists())
        self.assertEqual(self.dependency.read_bytes(), b'never remove or overwrite a dependency')
        self.assertFalse(list(self.workspace.glob('.kernel-verified-stage-*')))

    def test_both_roots_installed_with_exact_bytes_and_old_timestamps(self):
        result = self.install()
        self.assertEqual(result['status'], 'restored')
        self.assertEqual(result['modules'], ['A', 'B'])
        for path, data in self.fixture.outputs.items():
            output = self.workspace / path
            self.assertEqual(output.read_bytes(), data)
            self.assertLessEqual(output.stat().st_mtime, 1)
        self.assertTrue(self.dependency.is_file())
        self.assertFalse(list(self.workspace.glob('.kernel-verified-stage-*')))

    def test_changed_local_package_invalidates_its_root_consumer(self):
        current = copy.deepcopy(self.fixture.manifest['modules'])
        current['B']['inputs']['source_sha256'] = 'f' * 64
        self.assertEqual(self.install(current=current)['status'], 'cold')
        self.assert_cold()

    def test_changed_root_only_restores_independent_local_package(self):
        current = copy.deepcopy(self.fixture.manifest['modules'])
        current['A']['inputs']['source_sha256'] = 'f' * 64
        result = self.install(current=current)
        self.assertEqual(result['modules'], ['B'])
        self.assertFalse((self.workspace / '.lake/build').exists())
        self.assertTrue((self.workspace / 'lean/.lake/build/lib/lean/B.olean').is_file())

    def test_environment_change_restores_nothing(self):
        self.assertEqual(self.install(env={'compiler': 'different'})['status'], 'cold')
        self.assert_cold()

    def test_poisoned_output_leaves_no_installed_or_staged_files(self):
        outputs = dict(self.fixture.outputs)
        outputs['.lake/build/lib/lean/A.olean'] = b'bad'
        with self.assertRaises(ValueError):
            self.install(stream=self.fixture.archive(outputs=outputs))
        self.assert_cold()

    def test_existing_build_is_not_overwritten_or_cleaned(self):
        existing = self.workspace / 'lean/.lake/build/keep'
        existing.parent.mkdir(parents=True)
        existing.write_bytes(b'untouched')
        with self.assertRaisesRegex(ValueError, 'already exists'):
            self.install()
        self.assertEqual(existing.read_bytes(), b'untouched')
        self.assertFalse((self.workspace / '.lake/build').exists())

    def test_failure_installing_second_root_rolls_back_only_this_install(self):
        real_rename = os.rename
        calls = 0

        def fail_second(src, dst):
            nonlocal calls
            calls += 1
            if calls == 2:
                raise OSError('injected second-root failure')
            return real_rename(src, dst)

        with patch.object(restore.os, 'rename', side_effect=fail_second):
            with self.assertRaisesRegex(OSError, 'second-root'):
                self.install()
        self.assertEqual(calls, 3)  # First install, failed second, first rollback.
        self.assert_cold()

    def test_linked_build_parent_is_refused(self):
        # Mock the platform's link query so this refusal is exercised on Windows
        # even when its account cannot create symlinks. Linux integration must
        # also test an actual symlink/junction destination.
        original = Path.is_symlink
        target = self.workspace / 'lean/.lake'

        def is_link(path):
            return path == target or original(path)

        with patch.object(Path, 'is_symlink', is_link):
            with self.assertRaisesRegex(ValueError, 'Linked directory'):
                self.install()
        self.assert_cold()


if __name__ == '__main__':
    unittest.main()
