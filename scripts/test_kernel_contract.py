"""Tests of classification against immutable base commits, without Lean."""
import hashlib
import json
from pathlib import Path
import re
import tempfile
import unittest

from check_kernel_contract import ROOT, classify, git, tracked, validate


def external_input_reads(root):
    """Guard the scope rule's current no-file-read premise, including new Contrib files.

    This lexical guard is not a complete Lean effect analysis. Adding an
    intentional external input needs a reviewed contract/scope update first.
    """
    primitive = re.compile(r'include_str|include_bin|IO\s*\.\s*FS\s*\.|readFile|readBinFile|IO\s*\.\s*Process')
    found = []
    for path in tracked(root):
        if path.endswith('.lean') and (path == 'ZInQKernel.lean'
                or path.startswith(('ZInQKernel/', 'lean/', 'ThirdParty/'))):
            for line, text in enumerate((root / path).read_text(encoding='utf-8').splitlines(), 1):
                match = primitive.search(text)
                if match:
                    found.append(f'{path}:{line}: {match.group()}')
    return found


class CurrentInputTests(unittest.TestCase):
    def test_kernel_sources_have_no_unregistered_external_input_primitives(self):
        self.assertEqual(external_input_reads(ROOT), [],
                         'External input requires reviewed kernel contract and scope rules')


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

    def test_external_input_guard_reports_file_and_line(self):
        path = 'ZInQKernel/Contrib/External.lean'
        self.write(path, '-- fixture\n')
        self.commit()
        for primitive in ['include_str', 'include_bin', 'IO.FS.readFile',
                          'readFile', 'readBinFile', 'IO.Process.output', 'IO . FS . readFile']:
            with self.subTest(primitive=primitive):
                self.write(path, '-- fixture\n' + primitive + '\n')
                found = external_input_reads(self.root)
                self.assertEqual(len(found), 1)
                self.assertTrue(found[0].startswith(path + ':2: '))


if __name__ == "__main__":
    unittest.main()
