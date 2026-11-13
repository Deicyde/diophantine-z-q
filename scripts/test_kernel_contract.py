"""Tests of classification against immutable base commits, without Lean."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from check_kernel_contract import classify, git, validate


class ContractTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="kernel-contract-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        git(self.root, "init", "-q")
        git(self.root, "config", "user.name", "Contract test")
        git(self.root, "config", "user.email", "test@example.invalid")
        git(self.root, "config", "core.autocrlf", "false")
        self.write("ZInQKernel.lean", "import ZInQKernel.Target\n")
        self.write("ZInQKernel/Target.lean", "def Target : Prop := True\n")
        self.write("ThirdParty/GreenTao/Submission.lean", "-- vendor fixture\n")
        self.manifest = {"schema": "kernel-contract/v1", "files": {},
            "targets": [{"declaration": "Target", "provider": "Provider",
                         "source": "ZInQKernel/Target.lean"}], "exports": [], "headline": {}}
        for p in self.root.rglob("*.lean"):
            self.manifest["files"][p.relative_to(self.root).as_posix()] = hashlib.sha256(p.read_bytes()).hexdigest()
        self.save_manifest()
        self.commit()
        self.base = git(self.root, "rev-parse", "HEAD").decode().strip()

    def write(self, path, text):
        p = self.root / path
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8", newline="\n")

    def save_manifest(self):
        self.write("KERNEL_CONTRACT.json", json.dumps(self.manifest))

    def commit(self):
        git(self.root, "add", ".")
        git(self.root, "commit", "-qm", "fixture")

    def test_valid(self):
        self.assertFalse(validate(self.root)["acceptance"])

    def test_changed_body_rejected(self):
        self.write("ZInQKernel/Target.lean", "def Target : Prop := False\n")
        with self.assertRaisesRegex(ValueError, "Changed contract"):
            validate(self.root)

    def test_self_consistent_mutation_requires_review(self):
        self.write("ZInQKernel/Target.lean", "def Target : Prop := False\n")
        self.manifest["files"]["ZInQKernel/Target.lean"] = hashlib.sha256(
            (self.root / "ZInQKernel/Target.lean").read_bytes()).hexdigest()
        self.save_manifest()
        self.commit()
        validate(self.root)
        result = classify(self.root, self.base)
        self.assertEqual(result["route"], "statement_or_infrastructure_review")
        self.assertFalse(result["acceptance"])

    def test_contribution_discovered_and_queued_not_accepted(self):
        self.write("ZInQKernel/Contrib/One.lean", "-- a newly tracked module\n")
        self.commit()
        self.assertIn("ZInQKernel.Contrib.One", validate(self.root)["modules"])
        result = classify(self.root, self.base)
        self.assertEqual(result["route"], "proof_only_astra_review")
        self.assertFalse(result["acceptance"])

    def test_unregistered_baseline_rejected(self):
        self.write("ZInQKernel/Hidden.lean", "-- unregistered baseline\n")
        self.commit()
        with self.assertRaisesRegex(ValueError, "Unregistered baseline"):
            validate(self.root)

    def test_bypass_option_rejected(self):
        self.write("ZInQKernel/Contrib/One.lean", "-- skipKernel" + "TC\n")
        self.commit()
        with self.assertRaisesRegex(ValueError, "bypass option"):
            validate(self.root)

    def test_new_automation_is_not_proof_only(self):
        self.write(".github/workflows/other.yml", "name: new automation\n")
        self.commit()
        self.assertEqual(classify(self.root, self.base)["route"], "statement_or_infrastructure_review")


if __name__ == "__main__":
    unittest.main()
