#!/usr/bin/env python3
"""Adversarial integration tests using the actual pinned Lean kernel."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
LEAN = os.environ.get("KERNEL_TEST_LEAN", "lean")
AUDITOR = ROOT / "scripts/audit_kernel.lean"


class KernelAuditTests(unittest.TestCase):
    def fixture_env(self, directory):
        env = dict(os.environ)
        env["LEAN_PATH"] = str(directory)
        env["ELAN_TOOLCHAIN"] = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
        return env

    def run_modules(self, sources, owned, ok, message=None):
        with tempfile.TemporaryDirectory(prefix="kernel-audit-modules-") as tmp:
            d = Path(tmp)
            env = self.fixture_env(d)
            for name, source in sources:
                (d / (name + ".lean")).write_text(source, encoding="utf-8")
                built = subprocess.run([LEAN, "-o", name + ".olean", name + ".lean"],
                                       cwd=d, env=env, text=True, capture_output=True)
                self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
            spec = {"modules": owned, "targets": [{"declaration": "Fixture.Target",
                    "provider": "Fixture.holds"}], "exports": ["Fixture.headline"],
                    "headline": {"declaration": "Fixture.headline",
                                 "type_declaration": "Fixture.expected"}}
            (d / "spec.json").write_text(json.dumps(spec), encoding="utf-8")
            result = subprocess.run([LEAN, "--run", str(AUDITOR), "spec.json", "report.json"],
                                    cwd=d, env=env, text=True, capture_output=True)
            self.assertEqual(result.returncode == 0, ok, result.stdout + result.stderr)
            if message:
                self.assertIn(message, result.stdout + result.stderr)
            if ok:
                return json.loads((d / "report.json").read_text())

    fixture = ("namespace Fixture\ndef Target : Prop := True\n"
               "theorem expected : Target → Target := fun h => h\n"
               "theorem headline : Target → Target := fun h => h\nend Fixture\n")

    def run_case(self, suffix, ok, message=None, target="Fixture.Target", extra_headline=False):
        with tempfile.TemporaryDirectory(prefix="kernel-audit-") as tmp:
            d = Path(tmp)
            source = ("import Lean\nnamespace Fixture\n"
                      "def Target : Prop := True\n"
                      "theorem expected : Target → Target := fun h => h\n"
                      + ("theorem headline (_extra : False) : Target → Target := fun h => h\n"
                         if extra_headline else "theorem headline : Target → Target := fun h => h\n")
                      + suffix + "\nend Fixture\n")
            (d / "Fixture.lean").write_text(source, encoding="utf-8")
            env = dict(os.environ)
            env["LEAN_PATH"] = str(d)
            # Fixtures run outside the repository, so elan cannot discover its
            # lean-toolchain file by walking parent directories.
            env["ELAN_TOOLCHAIN"] = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
            build = subprocess.run([LEAN, "-o", "Fixture.olean", "Fixture.lean"],
                                   cwd=d, env=env, text=True, capture_output=True)
            self.assertEqual(build.returncode, 0, build.stdout + build.stderr)
            spec = {"modules": ["Fixture"], "targets": [{"declaration": target,
                    "provider": "Fixture.holds"}], "exports": ["Fixture.headline"],
                    "headline": {"declaration": "Fixture.headline",
                                 "type_declaration": "Fixture.expected"}}
            (d / "spec.json").write_text(json.dumps(spec), encoding="utf-8")
            result = subprocess.run([LEAN, "--run", str(AUDITOR), "spec.json", "report.json"],
                                    cwd=d, env=env, text=True, capture_output=True)
            self.assertEqual(result.returncode == 0, ok, result.stdout + result.stderr)
            if message:
                self.assertIn(message, result.stdout + result.stderr)
            if ok:
                return json.loads((d / "report.json").read_text())

    def test_exact_proof(self):
        report = self.run_case("theorem holds : Target := True.intro", True)
        self.assertEqual(report["targets"][0]["status"], "proved_exact_type")
        self.assertEqual(report["targets"][0]["type"], "True")
        self.assertFalse(report["protocol_acceptance"])

    def test_open_is_not_proved(self):
        self.assertEqual(self.run_case("", True)["targets"][0]["status"], "open")

    def test_explicit_assumption(self):
        self.run_case("theorem holds (h : Target) : Target := h", False, "Wrong full type")

    def test_implicit_assumption(self):
        self.run_case("theorem holds {h : Target} : Target := h", False, "Wrong full type")

    def test_instance_assumption(self):
        self.run_case("class HasTarget : Prop where\n  out : Target\n"
                      "theorem holds [h : HasTarget] : Target := h.out", False, "Wrong full type")

    def test_false_assumption(self):
        self.run_case("theorem holds (h : False) : Target := h.elim", False, "Wrong full type")

    def test_custom_axiom(self):
        self.run_case("axiom supplied : Target\ntheorem holds : Target := supplied", False,
                      "Forbidden axiom Fixture.supplied")

    def test_opaque_axiom_dependency(self):
        self.run_case("axiom supplied : Target\nopaque hidden : Target := supplied\n"
                      "theorem holds : Target := hidden", False, "Forbidden axiom Fixture.supplied")

    def test_headline_extra_premise(self):
        self.run_case("", False, "Wrong full type of Fixture.headline", extra_headline=True)

    def test_sorry(self):
        self.run_case("theorem holds : Target := by sorry", False, "Forbidden axiom sorryAx")

    def test_unrelated_axiom(self):
        self.run_case("theorem holds : Target := True.intro\naxiom unrelated : False", False,
                      "Forbidden axiom Fixture.unrelated")

    def test_missing_target(self):
        self.run_case("", False, "Missing target Fixture.NoSuchTarget", "Fixture.NoSuchTarget")

    def test_external_duplicate_theorem(self):
        report = self.run_modules([
            ("A", "import Lean\ntheorem shared : True := True.intro\n"),
            ("B", "import Lean\ntheorem shared : True := (fun h : True => h) True.intro\n"),
            ("C", "import A\nimport B\n" + self.fixture),
        ], ["C", "B"], True)
        self.assertGreaterEqual(report["duplicate_theorem_bodies_rechecked"], 1)

    def test_external_duplicate_cannot_hide_axiom(self):
        self.run_modules([
            ("BadLibrary", "import Lean\naxiom forbidden : True\n"),
            ("A", "import Lean\ntheorem shared : True := True.intro\n"),
            ("B", "import BadLibrary\ntheorem shared : True := forbidden\n"),
            ("C", "import A\nimport B\n" + self.fixture),
        ], ["C", "B"], False, "Forbidden axiom forbidden")

    def test_project_duplicates_in_both_import_orders(self):
        for imports in ("A B", "B A"):
            with self.subTest(imports=imports):
                report = self.run_modules([
                    ("A", "import Lean\ntheorem shared : True := True.intro\n"),
                    ("B", "import Lean\ntheorem shared : True := (fun h : True => h) True.intro\n"),
                    ("C", "".join("import " + m + "\n" for m in imports.split()) + self.fixture),
                ], ["C", "A", "B"], True)
                self.assertGreaterEqual(report["duplicate_theorem_bodies_rechecked"], 2)

    def test_project_duplicate_cannot_hide_axiom(self):
        for imports in ("A B", "B A"):
            with self.subTest(imports=imports):
                self.run_modules([
                    ("BadLibrary", "import Lean\naxiom forbidden : True\n"),
                    ("A", "import Lean\ntheorem shared : True := True.intro\n"),
                    ("B", "import BadLibrary\ntheorem shared : True := forbidden\n"),
                    ("C", "".join("import " + m + "\n" for m in imports.split()) + self.fixture),
                ], ["C", "A", "B"], False, "Forbidden axiom forbidden")

    def test_actual_project_module_in_external_closure(self):
        self.run_modules([
            ("Project", "import Lean\n" + self.fixture),
            ("External", "import Project\n"),
            ("C", "import External\n"),
        ], ["C", "Project"], False, "Project module leaked into external base: Project")

    def test_duplicate_body_is_kernel_checked(self):
        # Exercise an invalid serialized proof body directly. A source compiler
        # normally rejects it before serialization; a duplicate must still be
        # checked rather than inherit a valid copy from the imported environment.
        with tempfile.TemporaryDirectory(prefix="kernel-audit-body-") as tmp:
            d = Path(tmp)
            env = self.fixture_env(d)
            (d / "Auditor.lean").write_bytes(AUDITOR.read_bytes())
            built = subprocess.run([LEAN, "-o", "Auditor.olean", "Auditor.lean"],
                                   cwd=d, env=env, text=True, capture_output=True)
            self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
            for value, ok in (("True.intro", True), ("Nat.zero", False)):
                with self.subTest(value=value):
                    source = ("import Auditor\nopen Lean\n#eval do\n"
                              "  let env ← importModules #[{ module := `Lean, importAll := true }] {}\n"
                              "  let ci := ConstantInfo.thmInfo { name := `shared, levelParams := [], "
                              "type := mkConst `True, value := mkConst `" + value + ", all := [`shared] }\n"
                              "  checkDuplicateBody env.toKernelEnv ci 0\n")
                    (d / "Probe.lean").write_text(source, encoding="utf-8")
                    result = subprocess.run([LEAN, "Probe.lean"], cwd=d, env=env,
                                            text=True, capture_output=True)
                    self.assertEqual(result.returncode == 0, ok, result.stdout + result.stderr)
                    if not ok:
                        self.assertIn("Invalid duplicate theorem body shared", result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
