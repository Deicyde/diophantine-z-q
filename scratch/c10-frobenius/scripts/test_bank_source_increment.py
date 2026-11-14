#!/usr/bin/env python3
"""Archive integrity controls, not mathematical proof checks."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
import zipfile

from bank_source_increment import bank, safe_name


class BankingTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name) / 'base.zip'
        self.out = Path(self.temp.name) / 'increment.zip'
        self.payload = b'verified source fixture\n'
        self.manifest = {'files': {'Source.lean': {
            'bytes': len(self.payload), 'sha256': hashlib.sha256(self.payload).hexdigest()}}}
        self.save_base()

    def save_base(self):
        with zipfile.ZipFile(self.base, 'w') as archive:
            archive.writestr('Source.lean', self.payload)
            archive.writestr('MANIFEST.json', json.dumps(self.manifest))
        self.sha = hashlib.sha256(self.base.read_bytes()).hexdigest()

    def test_valid_increment_preserves_base(self):
        checksum = bank(self.base, self.out, {'New.lean': b'new fixture'}, {'commit': 'checked'},
                        self.sha)
        self.assertEqual(hashlib.sha256(self.base.read_bytes()).hexdigest(), self.sha)
        self.assertEqual(hashlib.sha256(self.out.read_bytes()).hexdigest(), checksum)
        with zipfile.ZipFile(self.out) as archive:
            self.assertEqual(archive.read('Source.lean'), self.payload)
            self.assertEqual(json.loads(archive.read('MANIFEST.json'))['commit'], 'checked')

    def test_wrong_base_checksum(self):
        with self.assertRaisesRegex(ValueError, 'Base archive checksum'):
            bank(self.base, self.out, {}, {}, '0' * 64)

    def test_corrupt_inner_manifest(self):
        self.manifest['files']['Source.lean']['sha256'] = '0' * 64
        self.save_base()
        with self.assertRaisesRegex(ValueError, 'Base file checksum'):
            bank(self.base, self.out, {}, {}, self.sha)

    def test_incomplete_manifest(self):
        self.manifest['files'] = {}
        self.save_base()
        with self.assertRaisesRegex(ValueError, 'exact file set'):
            bank(self.base, self.out, {}, {}, self.sha)

    def test_unsafe_addition_paths(self):
        for name in ['../outside', '/absolute', 'a/../outside', 'a//b']:
            with self.subTest(name=name), self.assertRaises(ValueError):
                safe_name(name)

    def test_no_manifest_override(self):
        with self.assertRaisesRegex(ValueError, 'must not be overridden'):
            bank(self.base, self.out, {}, {'files': {}}, self.sha)

    def test_base_cannot_be_overwritten(self):
        with self.assertRaisesRegex(ValueError, 'must not be overwritten'):
            bank(self.base, self.base, {}, {}, self.sha)


if __name__ == '__main__':
    unittest.main(verbosity=2)
