import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import kernel_build_packages as packages

GIT = shutil.which('git') or 'C:/Program Files/Git/cmd/git.exe'


class PackageTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root/'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
        (self.root/'lakefile.toml').write_text('name = "fixture"\n')
        self.dep = self.root/'.lake/packages/example'
        self.dep.mkdir(parents=True)
        (self.dep/'lakefile.toml').write_text('name = "example"\n')
        (self.dep/'Example.lean').write_text('def example := 1\n')
        for args in (['init', '-q'], ['add', '.'], ['-c', 'user.name=Test', '-c', 'user.email=test@example.invalid',
                                                 'commit', '-qm', 'Fixture']):
            subprocess.run([GIT, '-C', str(self.dep), *args], check=True, capture_output=True)
        self.rev = subprocess.check_output([GIT, '-C', str(self.dep), 'rev-parse', 'HEAD']).decode().strip()
        self.manifest = {'packagesDir': '.lake/packages', 'packages': [{
            'type': 'git', 'name': 'example', 'url': 'https://example.invalid/fixture', 'rev': self.rev,
            'configFile': 'lakefile.toml', 'manifestFile': 'lake-manifest.json', 'subDir': None}]}
        self.write_manifest()

    def write_manifest(self):
        (self.root/'lake-manifest.json').write_text(json.dumps(self.manifest))

    def inspect(self):
        return packages.package_environment(self.root, git_executable=GIT)

    def test_exact_clean_dependency_and_root_configuration_are_fingerprinted(self):
        result = self.inspect()
        self.assertEqual(result['packages']['example']['revision'], self.rev)
        before = result['configuration']['lakefile.toml']['sha256']
        (self.root/'lakefile.toml').write_text('name = "fixture"\nmoreLeanArgs = ["-DmaxRecDepth=10"]\n')
        self.assertNotEqual(before, self.inspect()['configuration']['lakefile.toml']['sha256'])

    def test_changed_source_or_wrong_revision_is_rejected(self):
        (self.dep/'Example.lean').write_text('def example := 2\n')
        with self.assertRaisesRegex(ValueError, 'Modified dependency'):
            self.inspect()
        (self.dep/'Example.lean').write_text('def example := 1\n')
        self.manifest['packages'][0]['rev'] = 'a'*40
        self.write_manifest()
        with self.assertRaisesRegex(ValueError, 'revision differs'):
            self.inspect()

    def test_local_package_configuration_and_manifest_are_bound(self):
        local = self.root/'lean'
        local.mkdir()
        (local/'lakefile.toml').write_text('name = "local"\n')
        (local/'lake-manifest.json').write_text('{"packages": []}\n')
        self.manifest['packages'].append({'type': 'path', 'name': 'local', 'dir': './lean',
                                         'configFile': 'lakefile.toml', 'manifestFile': 'lake-manifest.json'})
        self.write_manifest()
        self.assertEqual(self.inspect()['packages']['local']['location'], 'lean')
        self.manifest['packages'][-1]['dir'] = '../outside'
        self.write_manifest()
        with self.assertRaisesRegex(ValueError, 'escapes'):
            self.inspect()

    def test_redirected_git_worktree_cannot_validate_the_package_directory(self):
        other = self.root/'unrelated-worktree'
        other.mkdir()
        subprocess.run([GIT, '-C', str(self.dep), 'config', 'core.worktree', str(other)],
                       check=True, capture_output=True)
        with self.assertRaisesRegex(ValueError, 'worktree differs'):
            self.inspect()

    def test_branch_pin_ambiguous_config_and_unknown_kind_fail(self):
        self.manifest['packages'][0]['rev'] = 'main'
        self.write_manifest()
        with self.assertRaisesRegex(ValueError, 'exact commit'):
            self.inspect()
        self.manifest['packages'][0]['rev'] = self.rev
        self.manifest['packages'][0]['type'] = 'unknown'
        self.write_manifest()
        with self.assertRaisesRegex(ValueError, 'Unknown Lake'):
            self.inspect()
        (self.root/'lakefile.lean').write_text('-- ambiguous\n')
        with self.assertRaisesRegex(ValueError, 'ambiguous'):
            self.inspect()


if __name__ == '__main__':
    unittest.main()
