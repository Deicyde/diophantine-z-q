"""Negative controls for the manuscript-pole copy and its drift check, without Lean."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest

import check_manuscript_pole_copy
from check_manuscript_pole_copy import (COPY_DIR, PATCH, ROOT, STATEMENT, CopyError, compare, derive,
                                        git, parse_patch, read_sources, transform)


def main(argv):
    with contextlib.redirect_stdout(io.StringIO()):
        check_manuscript_pole_copy.main(argv)

CORE = """import ZInQKernel.Target

namespace ZInQ.Syntax

-- T1 of Route K
def poleT1 (A e : Nat) : Nat := A * (A + e)

end ZInQ.Syntax
"""
USE = """import ZInQKernel.Core
import ZInQKernel.Target

/-! A user of the template. `namespace Hidden` in a comment is not a command. -/

namespace ZInQ.Mult

open ZInQ.Syntax
open ZInQ.Syntax (poleT1)

namespace Inner
theorem use : poleT1 0 0 = 0 := rfl
end Inner

theorem _root_.ZInQ.Syntax.poleT1_zero : Syntax.poleT1 0 0 = 0 := rfl

end ZInQ.Mult
"""
SOURCES = {
    "ZInQKernel/Target.lean": "namespace ZInQ\ndef FrozenTarget : Prop := True\nend ZInQ\n",
    "ZInQKernel/Core.lean": CORE,
    "ZInQKernel/Use.lean": USE,
    "ZInQKernel/Side.lean": "import ZInQKernel.Core\n",
    "ZInQKernel/Main.lean": "import ZInQKernel.Use\nimport ZInQKernel.Target\n",
    "ZInQKernel/MainGreenTao.lean": "import ZInQKernel.Main\n",
    "ZInQKernel/Contrib/Other.lean": "import ZInQKernel.Core\n",
}
ROUTE = """# a note
--- a/ZInQKernel/Core.lean
+++ b/ZInQKernel/Core.lean
@@ -3,5 +3,5 @@
 namespace ZInQ.Syntax

--- T1 of Route K
-def poleT1 (A e : Nat) : Nat := A * (A + e)
+-- T1 of the manuscript
+def poleT1 (A e : Nat) : Nat := A * (A + 3 * e)

"""


class DerivationTests(unittest.TestCase):
    def test_copy_is_the_patched_dependents_of_the_headlines_and_nothing_else(self):
        before = dict(SOURCES)
        output, report = derive(SOURCES, ROUTE)
        self.assertEqual(SOURCES, before)
        self.assertEqual(sorted(output), sorted(
            [COPY_DIR + name for name in ("Core.lean", "Use.lean", "Main.lean", "MainGreenTao.lean")]
            + [STATEMENT]))
        self.assertEqual(report["patched"], ["ZInQKernel.Core"])
        core = output[COPY_DIR + "Core.lean"]
        self.assertIn("A * (A + 3 * e)", core)
        self.assertNotIn("A * (A + e)", core)
        self.assertIn("-- T1 of the manuscript", core)
        self.assertIn("import ZInQKernel.Target\n", core)
        self.assertIn("\nnamespace ManuscriptPole\nopen ManuscriptPole\n-- `open ZInQ.X` is written", core)
        self.assertIn("\nset_option linter.ambiguousOpen false\n\nnamespace ZInQ.Syntax\n", core)
        self.assertTrue(core.endswith("\nend ManuscriptPole\n"))

    def test_imports_namespaces_and_root_names_are_rewritten(self):
        use = derive(SOURCES, ROUTE)[0][COPY_DIR + "Use.lean"]
        self.assertIn("import ZInQKernel.Contrib.ManuscriptPole.Core\nimport ZInQKernel.Target\n", use)
        self.assertIn("namespace ZInQ.Mult\nopen _root_.ZInQ _root_.ZInQ.Mult\n", use)
        self.assertIn("namespace Inner\nopen _root_.ZInQ.Mult.Inner\n", use)
        self.assertIn("\nopen ZInQ.Syntax _root_.ZInQ.Syntax\n", use)
        self.assertNotIn("ManuscriptPole.ZInQ.Syntax end", use)
        self.assertIn("\nopen ZInQ.Syntax (poleT1)\n", use)
        self.assertIn("theorem _root_.ManuscriptPole.ZInQ.Syntax.poleT1_zero", use)
        for name in ("ZInQ.Mult", "ZInQ.Mult.Inner", "ZInQ.Syntax"):
            self.assertIn(f"\nnamespace {name} end {name}\n", use)
        self.assertNotIn("Hidden end", use)

    def test_a_changed_route_k_line_under_a_hunk_stops_the_derivation(self):
        for changed in (CORE.replace("A * (A + e)", "A * (A + e) + 0"),
                        CORE + "\nnamespace ZInQ.Syntax\n\n-- T1 of Route K\n"
                        + "def poleT1 (A e : Nat) : Nat := A * (A + e)\n\nend ZInQ.Syntax\n"):
            with self.subTest(changed=changed[-40:]):
                with self.assertRaisesRegex(CopyError, "no longer applies"):
                    derive({**SOURCES, "ZInQKernel/Core.lean": changed}, ROUTE)

    def test_invalid_patches_are_rejected(self):
        for bad, message in (
                (ROUTE.replace("@@ -3,5 +3,5 @@", "@@ -3,6 +3,5 @@"), "shorter than its header"),
                (ROUTE.replace("a/ZInQKernel/Core.lean", "/dev/null"), "only modify existing"),
                (ROUTE.replace("ZInQKernel/Core.lean", "ZInQKernel/Contrib/Other.lean"), "not a kernel module"),
                (ROUTE.replace("ZInQKernel/Core.lean", "ZInQKernel/Side.lean"), "no longer applies"),
                (ROUTE + ROUTE, "second section"),
                (ROUTE.replace("+-- T1 of the manuscript", "+-- T1 of Route K").replace(
                    "+def poleT1 (A e : Nat) : Nat := A * (A + 3 * e)",
                    "+def poleT1 (A e : Nat) : Nat := A * (A + e)"), "no-op hunk")):
            with self.subTest(message=message):
                with self.assertRaisesRegex(CopyError, message):
                    derive(SOURCES, bad)
        self.assertEqual(parse_patch(ROUTE)["ZInQKernel/Core.lean"][0][0][2], "-- T1 of Route K")

    def test_a_patched_module_no_headline_imports_is_an_error(self):
        side = ROUTE.replace("ZInQKernel/Core.lean", "ZInQKernel/Side.lean")
        sources = {**SOURCES, "ZInQKernel/Side.lean": CORE}
        with self.assertRaisesRegex(CopyError, "not imported by a headline"):
            derive(sources, side)

    def test_unsupported_source_forms_are_rejected(self):
        for text, message in (
                (USE.replace("Syntax.poleT1 0 0 = 0 := rfl", "_root_.ZInQ.Syntax.poleT1 0 0 = 0 := rfl"),
                 "_root_"),
                (USE.replace("end Inner", "end Outer"), "unbalanced"),
                (USE.replace("end ZInQ.Mult\n", ""), "unclosed"),
                (USE.replace("namespace ZInQ.Mult", "namespace Elsewhere"), "outside ZInQ"),
                (USE + "/- open\n", "unterminated")):
            with self.subTest(message=message):
                with self.assertRaisesRegex(CopyError, message):
                    transform("ZInQKernel/Use.lean", text, {"ZInQKernel.Core"}, "/- notice -/")


class DriftTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="manuscript-pole-copy-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        git(self.root, "init", "-q")
        git(self.root, "config", "core.autocrlf", "false")
        for path, text in {**SOURCES, PATCH: ROUTE}.items():
            self.write(path, text)
        self.output, _ = derive(read_sources(self.root), ROUTE)
        for path, text in self.output.items():
            self.write(path, text)

    def write(self, path, text):
        full = self.root / path
        full.parent.mkdir(parents=True, exist_ok=True)
        full.write_text(text, encoding="utf-8", newline="\n")
        git(self.root, "add", "--", path)

    def test_current_copy_passes_and_route_k_sources_are_never_written(self):
        self.assertEqual(compare(self.root, self.output), [])
        before = {p: (self.root / p).read_bytes() for p in SOURCES}
        main(["--root", str(self.root), "--write"])
        main(["--root", str(self.root)])
        self.assertEqual({p: (self.root / p).read_bytes() for p in SOURCES}, before)

    def test_edited_missing_untracked_and_stale_files_fail(self):
        target = COPY_DIR + "Use.lean"
        original = (self.root / target).read_text(encoding="utf-8")
        self.write(target, original.replace("poleT1 0 0", "poleT1 1 0"))
        self.assertEqual(compare(self.root, self.output), ["differs from its derivation: " + target])
        self.write(target, original)
        (self.root / target).unlink()
        self.assertEqual(compare(self.root, self.output), ["missing: " + target])
        self.write(target, original)
        self.write(COPY_DIR + "Old.lean", "-- left behind\n")
        self.assertEqual(compare(self.root, self.output), ["stale, no source derives it: " + COPY_DIR + "Old.lean"])
        with self.assertRaisesRegex(CopyError, "not its derivation"):
            main(["--root", str(self.root)])
        with self.assertRaisesRegex(CopyError, "not its derivation"):
            main(["--root", str(self.root), "--write"])
        self.assertTrue((self.root / COPY_DIR / "Old.lean").is_file())

    def test_a_route_k_edit_makes_the_tracked_copy_stale(self):
        self.write("ZInQKernel/Use.lean", USE.replace("theorem use", "theorem use'"))
        with self.assertRaisesRegex(CopyError, "not its derivation"):
            main(["--root", str(self.root)])


class RepositoryTests(unittest.TestCase):
    def test_no_route_k_module_imports_the_copy(self):
        prefix = "import ZInQKernel.Contrib.ManuscriptPole"
        users = [path for path, text in read_sources(ROOT).items() if prefix in text]
        self.assertEqual(users, [])


if __name__ == "__main__":
    unittest.main()
