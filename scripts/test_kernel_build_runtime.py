from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from kernel_build_environment import file_fingerprint
import kernel_build_runtime as runtime


class RuntimeTests(unittest.TestCase):
    def test_only_known_compiler_glibc_link_inputs_are_partitioned(self):
        with tempfile.TemporaryDirectory() as directory:
            compiler = Path(directory).resolve()
            inputs = [compiler/'lib/glibc/librt.so', compiler/'lib/glibc/unexpected.so',
                      compiler/'dependency/lib/glibc/librt.so', compiler/'lib/libleanshared.so']
            runtime_inputs, link_only = runtime.partition_link_inputs(inputs, compiler)
            self.assertEqual(link_only, inputs[:1])
            self.assertEqual(runtime_inputs, inputs[1:])
            self.assertEqual(runtime.partition_link_inputs(inputs, None), (inputs, []))

    def test_symbol_version_failure_remains_rejected_even_with_exit_zero(self):
        with self.assertRaisesRegex(ValueError, 'Unresolved or unrecognized'):
            runtime.parse_ldd("library: version `GLIBC_PRIVATE' not found\n"
                              "libc.so.6 => /lib/libc.so.6 (0x1234)\n", 0)

    def test_rejected_actual_response_records_path_exit_and_bounded_excerpt(self):
        response = subprocess.CompletedProcess([], 1, b'unrecognized library\n', b'X' * 5000)
        with patch.object(runtime.subprocess, 'run', return_value=response):
            with self.assertRaises(ValueError) as caught:
                runtime.loader_paths('/verified/tool', {'PATH': '/usr/bin:/bin'})
        message = str(caught.exception)
        self.assertIn('/verified/tool, exit 1', message)
        self.assertIn('unrecognized library', message)
        self.assertLess(len(message), 4500)

    def test_loader_paths_include_interpreter_and_transitive_libraries(self):
        # POSIX parsing is tested without invoking any supplied executable.
        text = ('linux-vdso.so.1 (0x00007ffff000)\n'
                'libm.so.6 => /lib/x86_64-linux-gnu/libm.so.6 (0x000071110000)\n'
                'libc.so.6 => /lib/x86_64-linux-gnu/libc.so.6 (0x000071220000)\n'
                '/lib64/ld-linux-x86-64.so.2 (0x000072330000)\n')
        with patch.object(runtime, 'Path', __import__('pathlib').PurePosixPath):
            self.assertEqual(runtime.parse_ldd(text, 0), [
                '/lib/x86_64-linux-gnu/libc.so.6', '/lib/x86_64-linux-gnu/libm.so.6',
                '/lib64/ld-linux-x86-64.so.2'])

    def test_unresolved_empty_and_unknown_output_never_establish_runtime_identity(self):
        for text, code in [('', 0), ('libbad.so => not found', 0), ('unexpected warning', 0),
                           ('linux-vdso.so.1 (0x1234)', 0), ('statically linked', 2)]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                runtime.parse_ldd(text, code)
        self.assertEqual(runtime.parse_ldd('statically linked', 0), [])
        self.assertEqual(runtime.parse_ldd('not a dynamic executable', 1), [])

    def test_only_exact_verified_native_files_are_selected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tool = root/'lean'; tool.write_bytes(b'\x7fELFtest fixture never executed')
            source = root/'file.lean'; source.write_text('def x := 1')
            expected = {p.name: file_fingerprint(root, p) for p in (tool, source)}
            self.assertEqual(runtime.native_inputs({str(root): expected}), [tool])
            tool.write_bytes(b'\x7fELFchanged')
            with self.assertRaisesRegex(ValueError, 'changed'):
                runtime.native_inputs({str(root): expected})

    def test_non_linux_or_credentialed_execution_stops_before_any_loader_call(self):
        with patch.object(runtime.platform, 'system', return_value='Windows'), \
                patch.object(runtime.subprocess, 'run') as run:
            with self.assertRaisesRegex(ValueError, 'requires Linux'):
                runtime.capture_runtime({}, ['/usr/bin/python3'], environ={})
            run.assert_not_called()
        for key in ('GH_TOKEN', 'LD_PRELOAD', 'LD_AUDIT', 'GLIBC_TUNABLES'):
            with self.subTest(key=key), patch.object(runtime.platform, 'system', return_value='Linux'), \
                    patch.object(runtime.subprocess, 'run') as run:
                with self.assertRaisesRegex(ValueError, 'unsupported loader'):
                    runtime.capture_runtime({}, ['/usr/bin/python3'], environ={key: 'test-only'})
                run.assert_not_called()

    @unittest.skipUnless(sys.platform.startswith('linux'), 'Actual ELF loader requires Linux')
    def test_actual_linux_loader_binds_copied_system_program_and_drivers(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            executable = root/'program'
            shutil.copyfile('/bin/true', executable)
            expected = {executable.name: file_fingerprint(root, executable)}
            identity, evidence = runtime.capture_runtime(
                {str(root): expected}, [str(Path(sys.executable).resolve()), '/bin/sh'], environ={})
            self.assertEqual(identity['schema'], 'kernel-linux-runtime/v1')
            self.assertTrue(evidence['selected'][str(executable)])
            self.assertIn('/etc/ld.so.cache', evidence['files'])
            self.assertIn('/usr/bin/ldd', evidence['files'])
            self.assertTrue(all(path in evidence['files'] for paths in evidence['selected'].values()
                                for path in paths))
            again, _ = runtime.capture_runtime(
                {str(root): expected}, [str(Path(sys.executable).resolve()), '/bin/sh'], environ={})
            self.assertEqual(identity, again)

    @unittest.skipUnless(sys.platform.startswith('linux'), 'Actual ELF loader requires Linux')
    def test_link_only_input_is_hashed_rechecked_and_cannot_be_loaded(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tool = root/'program'; shutil.copyfile('/bin/true', tool)
            link = root/'lib/glibc/librt.so'; link.parent.mkdir(parents=True)
            link.write_bytes(b'\x7fELFlink-only fixture must not be executed')
            files = {p.relative_to(root).as_posix(): file_fingerprint(root, p) for p in (tool, link)}
            identity, evidence = runtime.capture_runtime({str(root): files}, ['/bin/sh'],
                compiler_root=root, environ={})
            self.assertIn(str(link), evidence['compiler_link_only_inputs'])
            self.assertEqual(evidence['files'][str(link)], files['lib/glibc/librt.so'])
            self.assertNotIn(str(link), evidence['selected'])
            link.write_bytes(b'\x7fELFchanged link input')
            with self.assertRaisesRegex(ValueError, 'changed since fingerprinting'):
                runtime.capture_runtime({str(root): files}, ['/bin/sh'], compiler_root=root, environ={})
            files['lib/glibc/librt.so'] = file_fingerprint(root, link)
            with patch.object(runtime, 'loader_paths', return_value=[str(link)]):
                with self.assertRaisesRegex(ValueError, 'Runtime selected'):
                    runtime.capture_runtime({str(root): files}, ['/bin/sh'], compiler_root=root, environ={})


if __name__ == '__main__':
    unittest.main()
