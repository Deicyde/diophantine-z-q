#!/usr/bin/env python3
"""Negative controls for the offline compile guard; these do not run Lean."""
from pathlib import Path
import json
import subprocess
import sys
import tempfile
import unittest

CHECKER = Path(__file__).with_name('check_cached.py')
COMMIT = 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc'


class OfflineGuardTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='compile-guard-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.toolchain = self.root / 'toolchain'
        self.mathlib = self.root / 'mathlib'
        self.stacks = self.root / 'Stacks'
        self.source = self.root / 'Proof.lean'
        self.source.write_text('-- fixture, not a mathematical proof\n')
        self.marker = self.root / 'compiler-invoked'
        self.lean = self.toolchain / 'bin/lean'
        self.lean.parent.mkdir(parents=True)
        self.fake_compiler()
        self.artifacts = [
            self.mathlib / '.lake/build/lib/lean/Mathlib/CategoryTheory/Monoidal/Cartesian/Grp.olean',
            self.mathlib / '.lake/build/lib/lean/Mathlib/CategoryTheory/Monoidal/Cartesian/Over.olean',
            self.stacks / '.lake/build/lib/lean/StacksFrontier/AlgebraicGeometry/Variety/Frobenius/Twist.olean',
        ]
        for artifact in self.artifacts:
            artifact.parent.mkdir(parents=True, exist_ok=True)
            artifact.write_bytes(b'olean\x02\x014.35.0\0' + COMMIT.encode())

    def fake_compiler(self, commit=COMMIT, exit_code=0):
        code = (
            f'#!{sys.executable}\n'
            'from pathlib import Path\nimport os, sys, json\n'
            f'if sys.argv[1:] == ["--githash"]:\n    print({commit!r})\n    raise SystemExit(0)\n'
            'assert os.environ["LEAN_NUM_THREADS"] == "1"\n'
            'assert os.environ["LEAN_ABORT_ON_PANIC"] == "1"\n'
            f'Path({str(self.marker)!r}).write_text(json.dumps({{"argv": sys.argv[1:], '
            '"cwd": os.getcwd(), "lean_path": os.environ["LEAN_PATH"]}))\n'
            f'raise SystemExit({exit_code})\n'
        )
        self.lean.write_text(code)
        self.lean.chmod(0o755)

    def run_guard(self, *extra):
        return subprocess.run([
            sys.executable, str(CHECKER), '--toolchain', str(self.toolchain),
            '--mathlib', str(self.mathlib), '--stacks', str(self.stacks),
            *extra, str(self.source),
        ], capture_output=True, text=True, timeout=10)

    def test_valid_cached_imports_execute_only_the_requested_compiler(self):
        result = self.run_guard()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(self.marker.is_file())

    def test_wrong_compiler_commit_is_rejected_before_compile(self):
        self.fake_compiler(commit='0' * 40)
        result = self.run_guard()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('Unexpected Lean commit', result.stderr)
        self.assertFalse(self.marker.exists())

    def test_missing_cache_is_rejected_without_building_dependencies(self):
        self.artifacts[0].unlink()
        result = self.run_guard()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('Required prebuilt artifact is absent', result.stderr)
        self.assertFalse(self.marker.exists())

    def test_wrong_cached_version_is_rejected_before_compile(self):
        self.artifacts[1].write_bytes(b'olean\x02\x014.34.1\0' + COMMIT.encode())
        result = self.run_guard()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('Incompatible cached artifact header', result.stderr)
        self.assertFalse(self.marker.exists())

    def test_missing_explicit_dependency_path_is_rejected(self):
        result = self.run_guard('--dependency-lib', str(self.root / 'absent'))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('cached library directory is absent', result.stderr)
        self.assertFalse(self.marker.exists())

    def test_relative_toolchain_path_survives_compiler_workdir_change(self):
        result = subprocess.run([
            sys.executable, str(CHECKER), '--toolchain', 'toolchain',
            '--mathlib', 'mathlib', '--stacks', 'Stacks', 'Proof.lean',
        ], cwd=self.root, capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(self.marker.is_file())

    def test_native_nested_module_root_is_explicit(self):
        self.source = self.root / 'ZInQKernel/HDecomp/Objects.lean'
        self.source.parent.mkdir(parents=True)
        self.source.write_text('-- fixture, not a mathematical proof\n')
        result = self.run_guard('--source-root', str(self.root))
        self.assertEqual(result.returncode, 0, result.stderr)
        invocation = json.loads(self.marker.read_text())
        self.assertIn('--root=' + str(self.root.resolve()), invocation['argv'])
        self.assertEqual(invocation['cwd'], str(self.root.resolve()))
        self.assertIn(str(self.root.resolve()), invocation['lean_path'].split(':'))

    def test_missing_source_root_is_rejected_before_compile(self):
        result = self.run_guard('--source-root', str(self.root / 'missing-root'))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('source root is not an existing directory', result.stderr)
        self.assertFalse(self.marker.exists())

    def test_source_outside_root_is_rejected_before_compile(self):
        other = self.root / 'other-root'
        other.mkdir()
        result = self.run_guard('--source-root', str(other))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('source is outside the explicit package root', result.stderr)
        self.assertFalse(self.marker.exists())

    def test_compiler_failure_propagates(self):
        self.fake_compiler(exit_code=7)
        result = self.run_guard()
        self.assertEqual(result.returncode, 7)
        self.assertTrue(self.marker.is_file())


if __name__ == '__main__':
    unittest.main(verbosity=2)
