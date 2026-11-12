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


if __name__ == "__main__":
    unittest.main()
