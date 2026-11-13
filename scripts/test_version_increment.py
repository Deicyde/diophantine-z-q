"""Publication transitions on small real Git histories, plus trusted event routing."""
import copy
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

import check_current_manuscript as current
import check_version_increment as check


class PublicationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.git("init", "-q")
        self.git("config", "user.name", "Fixture")
        self.git("config", "user.email", "fixture@example.invalid")
        self.git("config", "core.autocrlf", "false")
        self.put("manuscripts/quartic_v15.tex", b"frozen earlier source")
        self.put("manuscripts/quartic_v15.pdf", b"%PDF-frozen earlier output")
        self.input = self.put("manuscripts/v16/proof.tex", b"frozen local proof")
        self.publish(16)
        self.git("add", ".")
        self.git("commit", "-qm", "Published Version 16")
        self.base = self.git("rev-parse", "HEAD").strip()

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.root, stderr=subprocess.STDOUT).decode()

    def put(self, name, raw):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
        return {"path": name, "sha256": current.sha(raw)}

    def publish(self, version, body="Proof.", pdf=None, inputs=None, suffix=""):
        source = ("\\documentclass{article}\n\\title{Example \\large Version " + str(version)
                  + "}\n\\begin{document}" + body + "\\end{document}\n").encode()
        self.profile = {"schema": "current-manuscript/v1", "version": version,
                        "tex": self.put(f"manuscripts/quartic_v{version}{suffix}.tex", source),
                        "pdf": self.put(f"manuscripts/quartic_v{version}{suffix}.pdf",
                                        pdf if pdf is not None else f"%PDF-1.4\nVersion {version}\n".encode()),
                        "required_tex_inputs": [self.input] if inputs is None else inputs}
        self.build = {"source": self.profile["tex"]["path"], "source_sha256": self.profile["tex"]["sha256"],
                      "pdf": self.profile["pdf"]["path"], "pdf_sha256": self.profile["pdf"]["sha256"],
                      "engine": "fixture", "bundle": "fixture", "tex_errors": 0, "unresolved_references": 0,
                      "manuscript_version": version}
        self.save()

    def save(self):
        self.profile["build_record"] = self.put(f"evidence/v{self.profile['version']}/BUILD.json",
                                                json.dumps(self.build).encode())
        self.put(current.PROFILE, json.dumps(self.profile).encode())

    def validate(self):
        return check.validate_transition(self.root, self.base)

    def test_unchanged_published_pair_retains_number(self):
        result = self.validate()
        self.assertFalse(result["published_content_changed"])
        self.assertEqual(result["version"], 16)

    def test_metadata_only_rebuild_retains_number(self):
        self.build["engine"] = "new recorded engine, identical output bytes"
        self.build["elapsed_seconds"] = 99
        self.save()
        self.assertFalse(self.validate()["published_content_changed"])

    def test_next_integer_and_draft_retries(self):
        self.publish(17, body="First draft")
        self.assertEqual(self.validate()["version"], 17)
        self.publish(17, body="Revised draft")
        self.assertEqual(self.validate()["version"], 17)

    def test_new_published_base_requires_next_integer_again(self):
        self.publish(17)
        self.git("add", ".")
        self.git("commit", "-qm", "Published Version 17")
        self.base = self.git("rev-parse", "HEAD").strip()
        self.publish(17, body="Another published revision")
        with self.assertRaisesRegex(ValueError, "expected Version 18"):
            self.validate()

    def test_source_change_without_increment_rejected(self):
        self.publish(16, body="Changed proof")
        with self.assertRaisesRegex(ValueError, "expected Version 17"):
            self.validate()

    def test_pdf_only_change_without_increment_rejected(self):
        self.publish(16, pdf=b"%PDF-different rendered content")
        with self.assertRaisesRegex(ValueError, "expected Version 17"):
            self.validate()

    def test_local_input_change_and_removal_require_increment(self):
        for inputs in ([self.put("manuscripts/new-part.tex", b"new proof part")], []):
            with self.subTest(inputs=inputs):
                self.publish(16, inputs=inputs)
                with self.assertRaisesRegex(ValueError, "expected Version 17"):
                    self.validate()

    def test_changed_input_in_new_path_preserves_previous_project(self):
        new_input = self.put("manuscripts/v17/proof.tex", b"revised proof")
        self.publish(17, inputs=[new_input])
        self.assertTrue(self.validate()["published_content_changed"])

    def test_skip_and_reverse_rejected(self):
        for version in (15, 18):
            with self.subTest(version=version):
                self.publish(version)
                with self.assertRaisesRegex(ValueError, "expected Version 17"):
                    self.validate()

    def test_relabel_unchanged_bytes_rejected(self):
        self.profile["version"] = 17
        self.build["manuscript_version"] = 17
        self.save()
        with self.assertRaisesRegex(ValueError, "edition"):
            self.validate()

    def test_bb_suffix_cannot_replace_integer_version(self):
        self.publish(17, suffix="_BB")
        with self.assertRaisesRegex(ValueError, "without a suffix"):
            self.validate()

    def test_string_version_rejected(self):
        self.profile["version"] = "17-BB"
        self.save()
        with self.assertRaisesRegex(ValueError, "Invalid manuscript version"):
            self.validate()

    def test_old_pair_and_current_published_input_cannot_be_rewritten(self):
        self.publish(17)
        for name in ("manuscripts/quartic_v16.tex", "manuscripts/quartic_v16.pdf",
                     "manuscripts/quartic_v15.tex", "manuscripts/quartic_v15.pdf"):
            with self.subTest(name=name):
                path = self.root / name
                original = path.read_bytes()
                path.write_bytes(original + b"changed")
                with self.assertRaisesRegex(ValueError, "rewritten or relabeled"):
                    self.validate()
                path.write_bytes(original)
        self.input = self.put("manuscripts/v16/proof.tex", b"rewritten published input")
        self.publish(17)
        with self.assertRaisesRegex(ValueError, "rewritten or relabeled"):
            self.validate()

    def test_old_pair_deletion_rejected(self):
        self.publish(17)
        (self.root / "manuscripts/quartic_v16.pdf").unlink()
        with self.assertRaisesRegex(ValueError, "Missing required file"):
            self.validate()

    def test_missing_base_does_not_fall_back_to_state_check(self):
        with self.assertRaisesRegex(ValueError, "Git baseline unavailable"):
            check.validate_transition(self.root, "a" * 40)

    def test_ci_rejects_explicit_local_baseline(self):
        with mock.patch.dict(os.environ, {"GITHUB_ACTIONS": "true"}), \
             mock.patch.object(sys, "argv", ["check", "--repo", str(self.root), "--base-ref", self.base]):
            with self.assertRaisesRegex(ValueError, "trusted GitHub event"):
                check.main()

    def test_ci_reads_external_event_and_fetches_only_its_base(self):
        with tempfile.TemporaryDirectory() as event_directory:
            event_path = Path(event_directory) / "event.json"
            event_path.write_text(json.dumps({
                "repository": {"full_name": "owner/project", "default_branch": "main"},
                "pull_request": {"base": {"sha": self.base, "ref": "main",
                                          "repo": {"full_name": "owner/project"}}},
                "candidate_selected_base": "f" * 40}))
            env = {"GITHUB_ACTIONS": "true", "GITHUB_WORKSPACE": str(self.root),
                   "GITHUB_EVENT_PATH": str(event_path), "GITHUB_EVENT_NAME": "pull_request",
                   "GITHUB_SHA": self.base, "GITHUB_REPOSITORY": "owner/project"}
            original_git = check.git
            fetches = []

            def transport(root, *args):
                if args[0] == "ls-remote":
                    return (self.base + "\trefs/heads/main\n").encode()
                if args[0] == "fetch":
                    fetches.append(args)
                    return b""
                return original_git(root, *args)

            with mock.patch.dict(os.environ, env), mock.patch.object(check, "git", side_effect=transport), \
                 mock.patch.object(sys, "argv", ["check", "--repo", str(self.root), "--github-event"]), \
                 mock.patch("sys.stdout", new=io.StringIO()) as output:
                check.main()
                report = json.loads(output.getvalue())
            self.assertEqual(fetches, [("fetch", "--no-tags", "--depth=1", "origin", self.base)])
            self.assertEqual(report["baseline_sha"], self.base)
            self.assertIn("trusted pull_request.base.sha", report["baseline_authority"])
            lookups = []

            def advancing_transport(root, *args):
                if args[0] == "ls-remote":
                    lookups.append(True)
                    revision = self.base if len(lookups) == 1 else "c" * 40
                    return (revision + "\trefs/heads/main\n").encode()
                return transport(root, *args)

            with mock.patch.dict(os.environ, env), mock.patch.object(check, "git", side_effect=advancing_transport), \
                 mock.patch.object(sys, "argv", ["check", "--repo", str(self.root), "--github-event"]):
                with self.assertRaisesRegex(ValueError, "advanced during validation"):
                    check.main()

    def test_ci_rejects_candidate_event_file(self):
        event_path = self.root / "candidate-event.json"
        event_path.write_text("{}")
        with mock.patch.dict(os.environ, {"GITHUB_ACTIONS": "true", "GITHUB_WORKSPACE": str(self.root),
                                         "GITHUB_EVENT_PATH": str(event_path)}), \
             mock.patch.object(sys, "argv", ["check", "--repo", str(self.root), "--github-event"]):
            with self.assertRaisesRegex(ValueError, "candidate repository"):
                check.main()


class TrustedEventTests(unittest.TestCase):
    def setUp(self):
        self.head = "b" * 40
        self.base = "a" * 40
        self.event = {"repository": {"full_name": "owner/project", "default_branch": "main"},
                      "pull_request": {"base": {"sha": self.base, "ref": "main",
                                                "repo": {"full_name": "owner/project"}}}}
        patch = mock.patch.object(check, "git", return_value=(self.head + "\n").encode())
        patch.start()
        self.addCleanup(patch.stop)

    def select(self, name, event=None, live=None):
        return check.event_baseline(Path("."), name, event or self.event, self.head,
                                    "owner/project", live_branch=lambda *_: live or self.base)

    def test_pr_uses_event_base_and_rejects_concurrent_base_advance(self):
        self.assertEqual(self.select("pull_request")[0], self.base)
        with self.assertRaisesRegex(ValueError, "base advanced"):
            self.select("pull_request", live="c" * 40)

    def test_default_push_uses_previous_published_sha(self):
        event = dict(self.event, ref="refs/heads/main", before=self.base, after=self.head)
        self.assertEqual(self.select("push", event)[0], self.base)

    def test_branch_retries_ignore_previous_draft_sha(self):
        event = dict(self.event, ref="refs/heads/proposal", before="d" * 40, after=self.head)
        self.assertEqual(self.select("push", event)[0], self.base)

    def test_nondefault_pr_uses_published_default_not_draft_base(self):
        event = copy.deepcopy(self.event)
        event["pull_request"]["base"].update(ref="integration", sha="d" * 40)
        self.assertEqual(self.select("pull_request", event)[0], self.base)

    def test_manual_main_and_tag_are_explicitly_state_only(self):
        for name, event in [("workflow_dispatch", dict(self.event, ref="main")),
                            ("push", dict(self.event, ref="refs/tags/v16", after=self.head))]:
            with self.subTest(name=name):
                baseline, authority = self.select(name, event)
                self.assertIsNone(baseline)
                self.assertIn("state check only", authority)

    def test_manual_branch_uses_published_default(self):
        self.assertEqual(self.select("workflow_dispatch", dict(self.event, ref="proposal"))[0], self.base)

    def test_wrong_checkout_or_repository_rejected(self):
        with mock.patch.object(check, "git", return_value=("c" * 40).encode()):
            with self.assertRaisesRegex(ValueError, "Checkout"):
                self.select("pull_request")
        event = copy.deepcopy(self.event)
        event["repository"]["full_name"] = "other/project"
        with self.assertRaisesRegex(ValueError, "repository"):
            self.select("pull_request", event)

    def test_missing_publication_base_and_unsupported_event_fail_closed(self):
        event = dict(self.event, ref="refs/heads/main", before="0" * 40, after=self.head)
        with self.assertRaisesRegex(ValueError, "nonzero"):
            self.select("push", event)
        with self.assertRaisesRegex(ValueError, "Unsupported event"):
            self.select("unrecognized")


if __name__ == "__main__":
    unittest.main()
