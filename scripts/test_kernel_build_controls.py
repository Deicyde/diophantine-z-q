import os
from pathlib import Path
import tempfile
import unittest

from kernel_build_controls import prepare_controls, verify_controls, SETTINGS


class ControlsTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.project = self.root/'project'; self.project.mkdir()
        self.controls = self.root/'controls'

    def test_configured_user_cache_is_not_read_or_modified(self):
        user = self.root/'user.toml'; user.write_text('existing user configuration')
        original = {'LAKE_CONFIG': str(user), 'LAKE_CACHE_DIR': 'old-cache',
                    'LAKE_CACHE_SERVICE': 'old-service', 'KEEP': 'same'}
        before = dict(original)
        environment, record = prepare_controls(self.project, self.controls, environ=original)
        self.assertEqual(original, before)
        self.assertEqual(user.read_text(), 'existing user configuration')
        self.assertEqual(environment['KEEP'], 'same')
        self.assertEqual(record, verify_controls(self.project, self.controls, environment))
        self.assertNotIn('LAKE_CACHE_SERVICE', environment)

    def test_controls_cannot_be_candidate_files_or_overwrite_an_existing_directory(self):
        for location in (self.project/'controls', self.root):
            with self.subTest(location=location), self.assertRaises(ValueError):
                prepare_controls(self.project, location, environ={})

    def test_modified_config_or_enabled_cache_is_rejected(self):
        environment, _ = prepare_controls(self.project, self.controls, environ={})
        for key in SETTINGS:
            changed = {**environment, key: 'unverified'}
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, 'cache controls'):
                verify_controls(self.project, self.controls, changed)
        (self.controls/'lake-config.toml').write_text('[cache]\ndefaultService="other"')
        with self.assertRaisesRegex(ValueError, 'empty Lake'):
            verify_controls(self.project, self.controls, environment)

    def test_credentials_are_not_silently_copied_or_removed(self):
        with self.assertRaisesRegex(ValueError, 'credentials'):
            prepare_controls(self.project, self.controls, environ={'GH_TOKEN': 'test-only'})
        self.assertFalse(self.controls.exists())
        environment, _ = prepare_controls(self.project, self.controls, environ={})
        with self.assertRaisesRegex(ValueError, 'credentials'):
            verify_controls(self.project, self.controls, {**environment, 'LAKE_CACHE_KEY': 'test-only'})

    def test_config_replacement_and_endpoint_override_are_rejected(self):
        environment, _ = prepare_controls(self.project, self.controls, environ={})
        for key, value in (('LAKE_CONFIG', str(self.root/'other')),
                           ('LAKE_CACHE_DIR', str(self.project/'.lake/cache')),
                           ('LAKE_CACHE_ARTIFACT_ENDPOINT', 'https://example.invalid')):
            with self.subTest(key=key), self.assertRaises(ValueError):
                verify_controls(self.project, self.controls, {**environment, key: value})

    def test_control_identity_is_portable_but_the_selected_file_is_exact(self):
        first, identity = prepare_controls(self.project, self.controls, environ={})
        second, other = prepare_controls(self.project, self.root/'second', environ={})
        self.assertEqual(identity, other)
        self.assertNotEqual(first['LAKE_CONFIG'], second['LAKE_CONFIG'])
        with self.assertRaises(ValueError):
            verify_controls(self.project, self.controls, second)


if __name__ == '__main__':
    unittest.main()
