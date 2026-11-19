import copy
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import kernel_build_metadata as metadata
from kernel_build_environment import fingerprint_tree


class MetadataTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.workspace = self.root/'workspace'; self.workspace.mkdir()
        self.prefix = self.root/'toolchain'; self.prefix.mkdir()
        self.dep = self.workspace/'.lake/packages/proofwidgets'; self.dep.mkdir(parents=True)
        self.build = self.dep/'.lake/build/lib/lean'; self.build.mkdir(parents=True)
        self.data = self.build/'A.olean'; self.data.write_bytes(b'compiled fixture; never executed')
        self.sidecar = self.build/'A.olean.hash'; self.sidecar.write_bytes(b'123')
        self.packages = {'packages': {'proofwidgets': {'type': 'git', 'location': '.lake/packages/proofwidgets', 'subdirectory': None}}}
        self.compiler = {'summary': {'sha256': 'a'*64}}
        self.expected = {'packages': copy.deepcopy(self.packages), 'toolchain': self.compiler['summary']}
        for module, name, value in [(metadata, 'package_environment', self.packages), (metadata, 'toolchain_inputs', self.compiler)]:
            mock = patch.object(module, name, return_value=value); mock.start(); self.addCleanup(mock.stop)
        env = patch.dict(os.environ, {}, clear=True); env.start(); self.addCleanup(env.stop)

    def prepare(self):
        return metadata.prepare_metadata(self.workspace, self.prefix, expected_environment=self.expected, environ={})

    def lock(self):
        lock = self.dep/'widget/package-lock.json'; lock.parent.mkdir()
        lock.write_bytes(b'{"test":"data only"}\r\n')
        return lock, lock.with_name(lock.name+'.hash')

    def test_zero_padding_preserves_data_and_mode_and_remains_in_full_fingerprint(self):
        data = self.data.read_bytes(); mode = self.sidecar.stat().st_mode
        result = self.prepare()
        self.assertEqual(self.sidecar.read_bytes(), b'0000000000000123')
        self.assertEqual(self.data.read_bytes(), data)
        self.assertEqual(self.sidecar.stat().st_mode, mode)
        self.assertEqual(result['changes'][0]['before_sha256'], hashlib.sha256(b'123').hexdigest())
        first, records = fingerprint_tree(self.dep)
        self.assertIn('.lake/build/lib/lean/A.olean.hash', records)
        self.sidecar.write_bytes(b'0000000000000124')
        self.assertNotEqual(fingerprint_tree(self.dep)[0], first)
        self.assertFalse(result['candidate_code_executed'])

    def test_second_preparation_is_inert_and_unrecognized_sidecar_is_not_repaired(self):
        self.prepare(); self.assertFalse(self.prepare()['changes'])
        for value in (b'', b'not hex', b'0'*17, b'ABC', b'123\n'):
            self.sidecar.write_bytes(value)
            self.assertFalse(self.prepare()['changes'])
            self.assertEqual(self.sidecar.read_bytes(), value)

    def test_nonbuild_source_sidecar_stays_untouched(self):
        outside = self.dep/'Source.lean.hash'; outside.write_bytes(b'123')
        self.prepare(); self.assertEqual(outside.read_bytes(), b'123')

    def test_missing_hash_is_computed_as_text_once_and_existing_value_is_never_overwritten(self):
        lock, sidecar = self.lock(); raw = lock.read_bytes()
        with patch.object(metadata, 'text_hash', return_value=b'1234567890abcdef') as helper:
            result = self.prepare(); self.prepare()
        helper.assert_called_once_with(self.prefix, lock)
        self.assertEqual(lock.read_bytes(), raw)
        self.assertEqual(sidecar.read_bytes(), b'1234567890abcdef')
        self.assertEqual(result['changes'][-1]['kind'], 'missing_text_hash')
        sidecar.write_bytes(b'existing-but-invalid')
        with patch.object(metadata, 'text_hash') as helper:
            self.prepare(); helper.assert_not_called()
        self.assertEqual(sidecar.read_bytes(), b'existing-but-invalid')

    def test_unverified_toolchain_or_package_stops_before_writes_or_execution(self):
        for key in ('toolchain','packages'):
            original = copy.deepcopy(self.expected)
            self.expected[key] = {'changed': True}
            with patch.object(metadata, 'text_hash') as helper:
                with self.assertRaisesRegex(ValueError, 'identity differs'): self.prepare()
                helper.assert_not_called()
            self.assertEqual(self.sidecar.read_bytes(), b'123')
            self.expected = original

    def test_credentials_stop_before_inspection(self):
        with patch.dict(os.environ, {'GH_TOKEN': 'fixture'}), patch.object(metadata, 'package_environment') as packages:
            with self.assertRaisesRegex(ValueError, 'credential-free'): self.prepare()
            packages.assert_not_called()

    def test_shared_sidecar_cannot_modify_another_file_through_a_hardlink(self):
        other = self.root/'other-file'
        try:
            os.link(self.sidecar, other)
        except OSError:
            self.skipTest('Host cannot create hardlinks')
        with self.assertRaisesRegex(ValueError, 'Shared cache sidecar'): self.prepare()
        self.assertEqual(other.read_bytes(), b'123')
        self.assertEqual(self.sidecar.read_bytes(), b'123')

    def test_missing_target_is_refused(self):
        self.data.unlink()
        with self.assertRaisesRegex(ValueError, 'no regular data file'): self.prepare()
        self.assertEqual(self.sidecar.read_bytes(), b'123')

    def test_changed_lockfile_during_helper_is_refused_before_sidecar_creation(self):
        lock, sidecar = self.lock()
        def changed(*args):
            lock.write_bytes(b'changed during read')
            return b'1234567890abcdef'
        with patch.object(metadata, 'text_hash', side_effect=changed):
            with self.assertRaisesRegex(ValueError, 'changed while hashing'): self.prepare()
        self.assertFalse(sidecar.exists())

    def test_hash_helper_has_no_candidate_paths_or_inherited_runtime_overrides(self):
        lock, _ = self.lock()
        def run(command, **kwargs):
            self.assertEqual(command[0], str(self.prefix/'bin'/('lean.exe' if os.name=='nt' else 'lean')))
            self.assertNotEqual(kwargs['cwd'], self.workspace)
            self.assertEqual(kwargs['env']['LEAN_PATH'], str(self.prefix/'lib/lean'))
            self.assertNotIn('LD_PRELOAD', kwargs['env'])
            self.assertNotIn('GH_TOKEN', kwargs['env'])
            source = Path(command[2]).read_text()
            self.assertIn('import Lake.Build.Trace', source)
            self.assertNotIn('ProofWidgets', source)
            return subprocess.CompletedProcess(command, 0, b'1234567890abcdef\n', b'')
        with patch.dict(os.environ, {'LD_PRELOAD':'hostile','LEAN_PATH':str(self.workspace),'GH_TOKEN':'fixture'}), \
                patch.object(metadata.subprocess, 'run', side_effect=run):
            self.assertEqual(metadata.text_hash(self.prefix, lock), b'1234567890abcdef')

    def test_failed_or_malformed_helper_output_is_refused(self):
        lock, _ = self.lock()
        for code, output in ((1,b'1234567890abcdef\n'),(0,b'abc\n'),(0,b'1234567890abcdef\nmore')):
            with patch.object(metadata.subprocess,'run',return_value=subprocess.CompletedProcess([],code,output,b'')):
                with self.assertRaisesRegex(ValueError,'could not be computed'): metadata.text_hash(self.prefix,lock)


class NativeMetadataTests(unittest.TestCase):
    def test_actual_toolchain_text_hash_normalizes_crlf_and_ignores_shadow_project_source(self):
        prefix = os.environ.get('KERNEL_METADATA_TEST_PREFIX')
        if not prefix:
            executable = shutil.which('lean')
            if not executable: self.skipTest('Installed pinned Lean toolchain unavailable')
            result = subprocess.run([executable,'--print-prefix'],capture_output=True,text=True,timeout=60)
            if result.returncode: self.skipTest('Installed Lean prefix unavailable')
            prefix = result.stdout.strip()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); data = root/'data.json'; data.write_bytes(b'one\r\ntwo\r\n')
            # An available fake source path must never become the helper import path.
            (root/'Lake/Build').mkdir(parents=True)
            (root/'Lake/Build/Trace.lean').write_text('this must never be read')
            with patch.dict(os.environ, {'LEAN_PATH':str(root)}):
                actual = metadata.text_hash(prefix,data)
                data.write_bytes(b'one\ntwo\n')
                self.assertEqual(actual,metadata.text_hash(prefix,data))
                data.write_bytes(b'different\n')
                self.assertNotEqual(actual,metadata.text_hash(prefix,data))
            self.assertRegex(actual.decode(),r'^[0-9a-f]{16}$')


if __name__ == '__main__': unittest.main()
