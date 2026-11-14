#!/usr/bin/env python3
"""Guard tests for output auditing; these are not mathematical proof evidence."""
import unittest

from audit_axiom_output import ALLOWED_AXIOMS, audit_reports

GOOD = "'A' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n"


class AuditOutputTests(unittest.TestCase):
    def test_multiline_reports(self):
        text = GOOD + "'B' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        self.assertEqual(audit_reports(text, ["A", "B"]), {"A": ALLOWED_AXIOMS, "B": ALLOWED_AXIOMS})

    def test_no_axioms(self):
        text = "'A' does not depend on any axioms\n'B' depends on axioms: []\n"
        self.assertEqual(audit_reports(text, ["A", "B"]), {"A": frozenset(), "B": frozenset()})

    def test_extra_axiom(self):
        with self.assertRaisesRegex(ValueError, "Unexpected axioms"):
            audit_reports(GOOD.replace("Quot.sound", "unprovedAssumption"), ["A"])

    def test_missing_report(self):
        with self.assertRaisesRegex(ValueError, "missing"):
            audit_reports(GOOD, ["A", "B"])

    def test_duplicate_report(self):
        with self.assertRaisesRegex(ValueError, "Duplicate"):
            audit_reports(GOOD + GOOD, ["A"])

    def test_extra_report(self):
        with self.assertRaisesRegex(ValueError, "extra"):
            audit_reports(GOOD + "'B' depends on axioms: []\n", ["A"])

    def test_diagnostics(self):
        for diagnostic in ["error: bad", "error(lean.unknownIdentifier): bad", "warning: bad"]:
            with self.subTest(diagnostic=diagnostic), self.assertRaisesRegex(ValueError, "warning"):
                audit_reports(GOOD + diagnostic, ["A"])

    def test_malformed_report(self):
        with self.assertRaisesRegex(ValueError, "Malformed"):
            audit_reports(GOOD + "'B' depends on axioms: no bracket\n", ["A", "B"])

    def test_bad_expected_names(self):
        for expected in [[], ["A", "A"]]:
            with self.subTest(expected=expected), self.assertRaisesRegex(ValueError, "unique"):
                audit_reports(GOOD, expected)


if __name__ == "__main__":
    unittest.main()
