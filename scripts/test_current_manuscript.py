"""Local fixtures for mandatory manuscript pairs and isolated TeX input staging."""
import copy
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock
from types import SimpleNamespace

import build_paper
import check_current_manuscript as check


class CurrentManuscriptTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        tex = b"\\documentclass{article}\n\\title{Example \\large Version 17}\n\\begin{document}Proof.\\end{document}\n"
        self.profile = {
            "schema": "current-manuscript/v1", "version": 17,
            "tex": self.put("manuscripts/current.tex", tex),
            "pdf": self.put("manuscripts/current.pdf", b"%PDF-1.4\nfixture\n"),
            "required_tex_inputs": [],
        }
        self.build = {"source": self.profile["tex"]["path"], "source_sha256": check.sha(tex),
                      "pdf": self.profile["pdf"]["path"], "pdf_sha256": self.profile["pdf"]["sha256"],
                      "engine": "Tectonic 0.17.0", "bundle": "fixture-bundle",
                      "tex_errors": 0, "unresolved_references": 0}
        self.save_build()
        self.save_profile()

    def put(self, name, raw):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
        return {"path": name, "sha256": check.sha(raw)}

    def save_build(self):
        self.profile["build_record"] = self.put("evidence/BUILD.json", json.dumps(self.build).encode())

    def save_profile(self):
        self.put(check.PROFILE, json.dumps(self.profile).encode())

    def test_valid_pair(self):
        _, _, report = check.validate(self.root)
        self.assertEqual(report["version"], 17)
        self.assertIn("independent review", report["scope"])

    def test_each_required_pair_member_missing(self):
        for role in ("tex", "pdf", "build_record"):
            with self.subTest(role=role):
                path = self.root / self.profile[role]["path"]
                raw = path.read_bytes()
                path.unlink()
                with self.assertRaisesRegex(ValueError, "Missing required file"):
                    check.validate(self.root)
                path.write_bytes(raw)

    def test_each_hash_is_checked(self):
        for role in ("tex", "pdf", "build_record"):
            with self.subTest(role=role):
                path = self.root / self.profile[role]["path"]
                raw = path.read_bytes()
                path.write_bytes(raw + b"changed")
                with self.assertRaisesRegex(ValueError, "SHA-256 mismatch"):
                    check.validate(self.root)
                path.write_bytes(raw)

    def test_wrong_edition(self):
        self.profile["version"] = 18
        self.save_profile()
        with self.assertRaisesRegex(ValueError, "edition"):
            check.validate(self.root)

    def test_comment_cannot_supply_edition(self):
        tex = b"\\documentclass{article}\n% \\title{Fake \\large Version 17}\n\\begin{document}Proof.\\end{document}"
        self.profile["tex"] = self.put("manuscripts/current.tex", tex)
        self.build["source_sha256"] = check.sha(tex)
        self.save_build()
        self.save_profile()
        with self.assertRaisesRegex(ValueError, "edition"):
            check.validate(self.root)

    def test_stale_build_mapping_even_when_record_hash_updated(self):
        original = copy.deepcopy(self.build)
        for field in ("source", "source_sha256", "pdf", "pdf_sha256"):
            with self.subTest(field=field):
                self.build = dict(original, **{field: "stale"})
                self.save_build()
                self.save_profile()
                with self.assertRaisesRegex(ValueError, "Stale build-record"):
                    check.validate(self.root)

    def test_failed_record_diagnostics(self):
        self.build["unresolved_references"] = 1
        self.save_build()
        self.save_profile()
        with self.assertRaisesRegex(ValueError, "diagnostics"):
            check.validate(self.root)

    def test_pdf_extension_is_not_enough(self):
        self.profile["pdf"] = self.put("manuscripts/current.pdf", b"not a PDF")
        self.build["pdf_sha256"] = self.profile["pdf"]["sha256"]
        self.save_build()
        self.save_profile()
        with self.assertRaisesRegex(ValueError, "not a PDF"):
            check.validate(self.root)

    def test_unsafe_paths_rejected(self):
        for name in ("../outside.tex", "/outside.tex", "C:/outside.tex", "manuscripts\\current.tex",
                     "manuscripts/../current.tex", "./manuscripts/current.tex", "manuscripts//current.tex",
                     "manuscripts/CON.tex", "manuscripts/current.tex "):
            with self.subTest(name=name):
                self.profile["tex"]["path"] = name
                self.save_profile()
                with self.assertRaisesRegex(ValueError, "[Uu]nsafe|Reserved"):
                    check.validate(self.root)

    def test_symlink_escape_rejected(self):
        outside = self.root.parent / (self.root.name + "-outside.tex")
        outside.write_text("outside")
        self.addCleanup(outside.unlink)
        link = self.root / "escape.tex"
        try:
            link.symlink_to(outside)
        except OSError as error:
            self.skipTest("Host does not permit creating test symlinks: " + str(error))
        with self.assertRaisesRegex(ValueError, "escapes repository"):
            check.safe_path(self.root, "escape.tex")

    def test_required_inputs_are_checked_and_staged_with_layout(self):
        extra = self.put("manuscripts/parts/proof.tex", b"A required proof part")
        graphics = self.put("figures/diagram.pdf", b"%PDF-fixture")
        self.profile["required_tex_inputs"] = [extra, graphics]
        self.save_profile()
        profile, contents, _ = check.validate(self.root)
        stage = self.root / "stage"
        build_paper.stage_project(stage, profile, contents)
        self.assertEqual((stage / extra["path"]).read_bytes(), b"A required proof part")
        self.assertEqual((stage / graphics["path"]).read_bytes(), b"%PDF-fixture")
        self.assertFalse((stage / profile["pdf"]["path"]).exists())
        self.assertFalse((stage / profile["build_record"]["path"]).exists())
        (self.root / extra["path"]).unlink()
        with self.assertRaisesRegex(ValueError, "Missing required file"):
            check.validate(self.root)

    def test_duplicate_input_rejected(self):
        self.profile["required_tex_inputs"] = [self.profile["tex"]]
        self.save_profile()
        with self.assertRaisesRegex(ValueError, "Duplicate artifact"):
            check.validate(self.root)

    def test_pair_failure_precedes_engine_install(self):
        (self.root / self.profile["pdf"]["path"]).unlink()
        with mock.patch.object(build_paper, "ROOT", self.root), mock.patch.object(build_paper, "install") as install:
            with mock.patch("sys.argv", ["build_paper.py"]), self.assertRaises(ValueError):
                build_paper.main()
            install.assert_not_called()

    def test_output_cannot_replace_published_pdf(self):
        pdf = (self.root / self.profile["pdf"]["path"]).read_bytes()
        self.profile["pdf"] = self.put("build/paper/current/current.pdf", pdf)
        self.build["pdf"] = self.profile["pdf"]["path"]
        self.save_build()
        self.save_profile()
        with mock.patch.object(build_paper, "ROOT", self.root), mock.patch.object(build_paper, "install") as install:
            with mock.patch("sys.argv", ["build_paper.py"]), self.assertRaisesRegex(ValueError, "overlaps"):
                build_paper.main()
            install.assert_not_called()
        self.assertEqual((self.root / self.profile["pdf"]["path"]).read_bytes(), pdf)

    def test_builder_uses_profile_safely_and_preserves_historical_outputs(self):
        original = self.root / self.profile["tex"]["path"]
        self.profile["tex"] = self.put("manuscripts/-current.tex", original.read_bytes())
        self.build["source"] = self.profile["tex"]["path"]
        self.save_build()
        self.save_profile()
        historical = self.root / "build/paper/compiler.log"
        historical.parent.mkdir(parents=True)
        historical.write_bytes(b"historical")
        cache = self.root / "cache"
        bundle_key = build_paper.BUNDLE.replace(":", ",58,").replace("/", ",47,")
        fingerprint = cache / "bundles/hashes" / bundle_key
        fingerprint.parent.mkdir(parents=True)
        fingerprint.write_text(build_paper.BUNDLE_DIGEST)

        def compiler(command, *, cwd, **kwargs):
            self.assertEqual(command[-1], "./-current.tex")
            self.assertEqual((cwd / "-current.tex").read_bytes(), original.read_bytes())
            (cwd / "-current.log").write_text("successful fixture build")
            (cwd / "-current.pdf").write_bytes(b"%PDF-fresh fixture")
            return SimpleNamespace(returncode=0)

        args = ["build_paper.py", "--tectonic", str(self.root / "fixture-engine"), "--cache", str(cache)]
        with mock.patch.object(build_paper, "ROOT", self.root), mock.patch("sys.argv", args), \
             mock.patch.object(build_paper.subprocess, "check_output", return_value="Tectonic 0.17.0"), \
             mock.patch.object(build_paper.subprocess, "run", side_effect=compiler), mock.patch("sys.stdout", new=io.StringIO()):
            build_paper.main()
        self.assertEqual(historical.read_bytes(), b"historical")
        receipt = json.loads((self.root / "build/paper/current/build-report.json").read_bytes())
        self.assertEqual(receipt["manuscript_version"], 17)
        self.assertFalse(receipt["byte_identity_to_published_pdf"])
        self.assertEqual((self.root / self.profile["pdf"]["path"]).read_bytes(), b"%PDF-1.4\nfixture\n")


if __name__ == "__main__":
    unittest.main()
