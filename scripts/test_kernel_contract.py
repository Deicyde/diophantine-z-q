"""Tests of classification against immutable base commits, without Lean."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from check_kernel_contract import classify, git, regenerate, validate


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

    def test_regenerate_is_identity_on_valid_manifest(self):
        before = (self.root / "KERNEL_CONTRACT.json").read_bytes()
        self.assertEqual(regenerate(self.root), {"added": [], "removed": [], "changed": []})
        self.assertEqual(json.loads((self.root / "KERNEL_CONTRACT.json").read_bytes()), json.loads(before))

    def test_regenerate_registers_baseline_change_for_review(self):
        self.write("ZInQKernel/Target.lean", "def Target : Prop := False\n")
        self.write("ZInQKernel/New.lean", "-- a new baseline module\n")
        self.write("ZInQKernel/Contrib/One.lean", "-- a contribution stays unpinned\n")
        (self.root / "ThirdParty/GreenTao/Submission.lean").unlink()
        self.write("ThirdParty/GreenTao/Submission/Basic.lean", "-- replacement vendor root module\n")
        self.write("ThirdParty/GreenTao/Submission.lean", "-- vendor fixture, edited\n")
        git(self.root, "add", "-A")
        changes = regenerate(self.root)
        self.assertEqual(changes["added"], ["ThirdParty/GreenTao/Submission/Basic.lean", "ZInQKernel/New.lean"])
        self.assertEqual(changes["changed"], ["ThirdParty/GreenTao/Submission.lean", "ZInQKernel/Target.lean"])
        manifest = json.loads((self.root / "KERNEL_CONTRACT.json").read_bytes())
        self.assertNotIn("ZInQKernel/Contrib/One.lean", manifest["files"])
        self.assertEqual(manifest["targets"], self.manifest["targets"])
        self.commit()
        validate(self.root)
        self.assertEqual(classify(self.root, self.base)["route"], "statement_or_infrastructure_review")

    def test_regenerate_drops_deleted_source(self):
        self.write("ZInQKernel/Extra.lean", "-- extra\n")
        git(self.root, "add", "-A")
        regenerate(self.root)
        self.commit()
        git(self.root, "rm", "-q", "ZInQKernel/Extra.lean")
        self.assertEqual(regenerate(self.root)["removed"], ["ZInQKernel/Extra.lean"])
        self.commit()
        validate(self.root)


if __name__ == "__main__":
    unittest.main()
