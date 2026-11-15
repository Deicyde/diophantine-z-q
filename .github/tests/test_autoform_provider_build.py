"""Static regression tests for .github/workflows/autoform-verify.yml.

They check that the blueprint provider modules are built by module name after
the default build and before `lake pack`, that these tests run early, that the
audit keeps its stages (now with elapsed-time markers), and that the critical
guards stay as they are. Standard library only: the workflow is read with a
small parser for the YAML subset it uses, and each run script is split into
logical shell commands, so checks address one step and one command at a time.
A scoped import-closure check reads only the `import` header of the PSide
provider modules, to show which PSide modules the named targets build.
Nothing here needs Git history, a network or a Lean toolchain; the checks that
need the Lean sources skip only when no ZInQKernel tree is checked out at all,
and fail when the tree is present but a provider source is missing.
"""

from __future__ import annotations

import fnmatch
import os
import re
import shlex
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path
from typing import Callable, Iterable

GITHUB_DIR = Path(__file__).resolve().parents[1]
REPO_ROOT = GITHUB_DIR.parent
WORKFLOW = GITHUB_DIR / "workflows" / "autoform-verify.yml"

PSIDE_PREFIX = "ZInQKernel.Contrib.PSide."
PSIDE_TARGETS = (
    "ZInQKernel.Contrib.PSide.Convergence",
    "ZInQKernel.Contrib.PSide.Supersingular",
    "ZInQKernel.Contrib.PSide.BadPrimes",
)
# The six PSide modules that declare the 49 PSide names the blueprint audit
# reported missing (Convergence 8, Hasse 10, Coeff 15, APZero 7, BadPrimes 6,
# Supersingular 3). Listed on its own, not derived from PSIDE_TARGETS, so
# dropping a target from both the workflow and that tuple still fails.
PSIDE_BUILT = frozenset({
    "ZInQKernel.Contrib.PSide.Convergence",
    "ZInQKernel.Contrib.PSide.Hasse",
    "ZInQKernel.Contrib.PSide.Coeff",
    "ZInQKernel.Contrib.PSide.APZero",
    "ZInQKernel.Contrib.PSide.BadPrimes",
    "ZInQKernel.Contrib.PSide.Supersingular",
})
PROVIDER_MODULES = (
    "ZInQKernel.Contrib.GaussFE.Headline",
    "ZInQKernel.Contrib.HeckeAll.Provider",
) + PSIDE_TARGETS
MODULE_SELECTOR = re.compile(r"^\+ZInQKernel(\.[A-Z][A-Za-z0-9_]*)+$")

CHECKOUT = "actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1"
SETUP_UV = "astral-sh/setup-uv@c771a70e6277c0a99b617c7a806ffedaca235ff9"
UPLOAD = "actions/upload-artifact@cf430e030ddbb5b0abf93d22962f4752f3646cd9"

AUDIT_STAGES = [
    "lake pack",
    "policy and assumptions extraction",
    "archive parsing and probe generation",
    "LEAN_PATH lookup",
    "axiom probe run",
]


# --- A parser for the YAML subset the workflow uses -------------------------


class Block(str):
    """A block scalar (`|` or `>-`) that remembers its style."""

    style: str

    def __new__(cls, text: str, style: str) -> "Block":
        value = super().__new__(cls, text)
        value.style = style
        return value


class WorkflowParser:
    """Block mappings, block sequences of mappings, plain or quoted scalars and
    `|`/`>` block scalars. Anything else raises, so a workflow edit outside
    this subset fails loudly instead of being misread."""

    def __init__(self, text: str) -> None:
        self.lines = text.splitlines()
        self.i = 0

    @staticmethod
    def _indent(line: str) -> int:
        return len(line) - len(line.lstrip(" "))

    def _peek(self):
        while self.i < len(self.lines):
            stripped = self.lines[self.i].strip()
            if stripped and not stripped.startswith("#"):
                line = self.lines[self.i]
                if "\t" in line[: self._indent(line) + 1]:
                    raise ValueError(f"tab indentation at line {self.i + 1}")
                return self._indent(line), stripped
            self.i += 1
        return None

    def parse(self):
        first = self._peek()
        if first is None or first[0] != 0:
            raise ValueError("workflow must start with a top-level mapping")
        result = self._mapping(0)
        if self._peek() is not None:
            raise ValueError(f"unparsed content at line {self.i + 1}")
        return result

    def _node(self, indent: int):
        _, content = self._peek()
        if content.startswith("- "):
            return self._sequence(indent)
        return self._mapping(indent)

    def _mapping(self, indent: int, into: dict | None = None) -> dict:
        result = {} if into is None else into
        while True:
            nxt = self._peek()
            if nxt is None or nxt[0] < indent:
                return result
            if nxt[0] > indent or nxt[1].startswith("- "):
                raise ValueError(f"unexpected structure at line {self.i + 1}")
            self.i += 1
            self._entry(result, nxt[1], indent)

    def _sequence(self, indent: int) -> list:
        items = []
        while True:
            nxt = self._peek()
            if nxt is None or nxt[0] < indent:
                return items
            if nxt[0] > indent or not nxt[1].startswith("- "):
                raise ValueError(f"unexpected structure at line {self.i + 1}")
            self.i += 1
            item: dict = {}
            self._entry(item, nxt[1][2:].strip(), indent + 2)
            self._mapping(indent + 2, item)
            items.append(item)

    def _entry(self, result: dict, content: str, indent: int) -> None:
        key, sep, rest = content.partition(":")
        key, rest = key.strip(), rest.strip()
        if not sep or not key:
            raise ValueError(f"expected 'key: value' at line {self.i}")
        if key in result:
            raise ValueError(f"duplicate key {key!r} at line {self.i}")
        if rest in ("|", "|-", ">", ">-"):
            result[key] = self._block_scalar(indent, rest)
        elif rest == "" or rest.startswith("#"):
            nxt = self._peek()
            if nxt is not None and nxt[0] > indent:
                result[key] = self._node(nxt[0])
            elif nxt is not None and nxt[0] == indent and nxt[1].startswith("- "):
                result[key] = self._sequence(indent)
            else:
                result[key] = None
        else:
            result[key] = self._scalar(rest)

    def _block_scalar(self, parent_indent: int, style: str) -> Block:
        raw = []
        while self.i < len(self.lines):
            line = self.lines[self.i]
            if line.strip() and self._indent(line) <= parent_indent:
                break
            raw.append(line)
            self.i += 1
        while raw and not raw[-1].strip():
            raw.pop()
        if not raw:
            raise ValueError(f"empty block scalar before line {self.i + 1}")
        body_indent = min(self._indent(line) for line in raw if line.strip())
        body = [line[body_indent:] for line in raw]
        if style.startswith(">"):
            return Block(" ".join(line.strip() for line in body if line.strip()), style)
        return Block("\n".join(body) + "\n", style)

    @staticmethod
    def _scalar(text: str) -> str:
        if text[0] in "\"'":
            end = text.find(text[0], 1)
            if end < 0:
                raise ValueError(f"unterminated quoted scalar: {text}")
            return text[1:end]
        return re.split(r"\s+#", text, maxsplit=1)[0].strip()


def logical_commands(script: str) -> list[str]:
    """Shell lines with comments and blanks removed and continuations joined."""
    commands, pending = [], ""
    for raw in script.splitlines():
        line = raw.strip()
        if not pending and (not line or line.startswith("#")):
            continue
        if line.endswith("\\"):
            pending += line[:-1].rstrip() + " "
            continue
        commands.append((pending + line).strip())
        pending = ""
    if pending:
        commands.append(pending.strip())
    return commands


def words(command: str) -> list[str]:
    try:
        return shlex.split(command)
    except ValueError:
        return []


def is_lake_build(command: str) -> bool:
    return words(command)[:2] == ["lake", "build"]


# --- A scoped reader for Lean module import headers --------------------------

_IMPORT_MODIFIERS = {"public", "private", "meta", "all"}


def header_imports(text: str) -> list[str]:
    """Modules named by the `import` lines of a Lean file's header.

    Reading stops at the first line that is not blank, a comment, `module`,
    `prelude` or an import, so text later in the file is never read as one."""
    imports: list[str] = []
    depth = 0
    for raw in text.splitlines():
        line = raw.strip()
        while line:
            if depth:
                opened, closed = line.find("/-"), line.find("-/")
                if closed < 0 and opened < 0:
                    line = ""
                elif opened >= 0 and (closed < 0 or opened < closed):
                    depth, line = depth + 1, line[opened + 2:]
                else:
                    depth, line = depth - 1, line[closed + 2:].strip()
            elif line.startswith("/-"):
                depth, line = 1, line[2:]
            else:
                break
        if depth or not line or line.startswith("--"):
            continue
        tokens = line.split("--", 1)[0].split()
        if tokens in (["module"], ["prelude"]):
            continue
        while tokens and tokens[0] in _IMPORT_MODIFIERS - {"all"}:
            tokens = tokens[1:]
        if not tokens or tokens[0] != "import":
            break
        imports.extend(token for token in tokens[1:] if token not in _IMPORT_MODIFIERS)
    return imports


def import_closure(roots: Iterable[str], read_imports: Callable[[str], list[str]], prefix: str) -> set[str]:
    """Modules under `prefix` reachable from `roots` through imports. A module
    whose source cannot be read raises instead of being dropped."""
    seen: set[str] = set()
    pending = [root for root in roots if root.startswith(prefix)]
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        pending.extend(name for name in read_imports(module) if name.startswith(prefix))
    return seen


def module_source(module: str) -> Path:
    return REPO_ROOT.joinpath(*module.split(".")).with_suffix(".lean")


def read_module_imports(module: str) -> list[str]:
    return header_imports(module_source(module).read_text(encoding="utf-8"))


# --- Fixtures ----------------------------------------------------------------


class WorkflowTestCase(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.workflow = WorkflowParser(WORKFLOW.read_text(encoding="utf-8")).parse()
        cls.job = cls.workflow["jobs"]["build"]
        cls.steps = cls.job["steps"]
        cls.names = [step.get("name") for step in cls.steps]

    def step(self, name: str) -> dict:
        matches = [step for step in self.steps if step.get("name") == name]
        self.assertEqual(len(matches), 1, f"expected exactly one step named {name!r}")
        return matches[0]

    def index(self, name: str) -> int:
        self.step(name)
        return self.names.index(name)

    def commands(self, name: str) -> list[str]:
        return logical_commands(self.step(name)["run"])

    def first_index(self, commands: list[str], predicate, what: str, start: int = 0) -> int:
        for position in range(start, len(commands)):
            if predicate(commands[position]):
                return position
        self.fail(f"no command for {what}")


# --- Tests -------------------------------------------------------------------


class ParserTest(unittest.TestCase):
    def test_parses_steps_scalars_and_blocks(self) -> None:
        text = (
            "jobs:\n"
            "  build:\n"
            "    timeout-minutes: 7\n"
            "    steps:\n"
            "      - name: one # trailing\n"
            "        uses: a/b@123 # v1\n"
            "        with:\n"
            "          version: \"1.0\"\n"
            "      # comment between steps\n"
            "      - name: two\n"
            "        run: |\n"
            "          set -euo pipefail\n"
            "          # kept inside the block\n"
            "          echo a \\\n"
            "            b\n"
            "      - name: three\n"
            "        run: >-\n"
            "          x\n"
            "          y\n"
        )
        steps = WorkflowParser(text).parse()["jobs"]["build"]["steps"]
        self.assertEqual([step["name"] for step in steps], ["one", "two", "three"])
        self.assertEqual(steps[0]["uses"], "a/b@123")
        self.assertEqual(steps[0]["with"], {"version": "1.0"})
        self.assertEqual(steps[1]["run"].style, "|")
        self.assertEqual(logical_commands(steps[1]["run"]), ["set -euo pipefail", "echo a b"])
        self.assertEqual(steps[2]["run"], "x y")

    def test_rejects_duplicate_keys_and_stray_indentation(self) -> None:
        with self.assertRaises(ValueError):
            WorkflowParser("a: 1\na: 2\n").parse()
        with self.assertRaises(ValueError):
            WorkflowParser("a:\n  b: 1\n    c: 2\n").parse()


class EarlyUnitTestsTest(WorkflowTestCase):
    NAME = "Run workflow and audit unit tests"

    def test_runs_right_after_checkout(self) -> None:
        self.assertEqual(self.steps[0].get("uses"), CHECKOUT)
        self.assertEqual(self.index(self.NAME), 1)

    def test_discovers_stdlib_tests_under_github_tests(self) -> None:
        (command,) = self.commands(self.NAME)
        argv = words(command)
        self.assertEqual(argv[:4], ["python3", "-m", "unittest", "discover"])
        options = {}
        for flag, value in zip(argv, argv[1:]):
            options[flag] = value
        start = options.get("--start-directory", options.get("-s"))
        pattern = options.get("--pattern", options.get("-p"))
        self.assertEqual(start, ".github/tests")
        self.assertEqual(pattern, "test_autoform_*.py")
        # This file is one of the discovered tests.
        self.assertEqual((REPO_ROOT / start).resolve(), Path(__file__).resolve().parent)
        self.assertTrue(fnmatch.fnmatch(Path(__file__).name, pattern))

    def test_precedes_every_expensive_step(self) -> None:
        early = self.index(self.NAME)
        for position, step in enumerate(self.steps):
            uses = step.get("uses") or ""
            run = step.get("run") or ""
            expensive = (uses and uses != CHECKOUT) or re.search(r"\b(uvx|lake|curl|lean|elan)\b", run)
            if expensive:
                self.assertGreater(position, early, f"step {step.get('name')!r} runs before the unit tests")


class ProviderBuildTest(WorkflowTestCase):
    NAME = "Build blueprint provider modules"

    def provider_command(self) -> list[str]:
        builds = [cmd for cmd in self.commands(self.NAME) if is_lake_build(cmd)]
        self.assertEqual(len(builds), 1)
        return words(builds[0])

    def test_builds_every_provider_module_by_module_selector(self) -> None:
        targets = self.provider_command()[2:]
        self.assertEqual(len(targets), len(set(targets)), "a provider target is named twice")
        self.assertEqual(sorted(targets), sorted("+" + module for module in PROVIDER_MODULES))
        for target in targets:
            self.assertRegex(target, MODULE_SELECTOR)
            # Module paths start at the ZInQKernel source root, not at the
            # ZInQ declaration namespace.
            self.assertFalse(target.startswith("+ZInQ."), target)

    def test_pside_targets_are_built_before_pack(self) -> None:
        targets = self.provider_command()[2:]
        for module in PSIDE_TARGETS:
            self.assertIn("+" + module, targets)
        self.assertLess(self.index(self.NAME), self.index("Audit every root-package declaration"))
        # No other step builds a named module, so the selection lives in one place.
        for step in self.steps:
            if step.get("name") != self.NAME:
                for command in logical_commands(step.get("run") or ""):
                    if is_lake_build(command):
                        self.assertEqual(words(command), ["lake", "build"], step.get("name"))

    def test_step_fails_fast(self) -> None:
        run = self.step(self.NAME)["run"]
        self.assertEqual(run.style, "|")
        self.assertEqual(self.commands(self.NAME)[0], "set -euo pipefail")

    def test_ordered_after_default_build_and_before_pack(self) -> None:
        build_lean = self.commands("Build Lean")
        clean = self.first_index(build_lean, lambda c: c == 'lake clean "$root_package"', "root clean")
        default_build = self.first_index(build_lean, lambda c: c == "lake build", "default build", clean + 1)
        self.assertEqual(default_build, len(build_lean) - 1, "the default build stays last in Build Lean")
        self.assertEqual(self.index(self.NAME), self.index("Build Lean") + 1)
        self.assertEqual(self.index("Audit every root-package declaration"), self.index(self.NAME) + 1)
        audit = self.commands("Audit every root-package declaration")
        first_lake = self.first_index(audit, lambda c: words(c)[:1] == ["lake"], "first lake command")
        self.assertEqual(audit[first_lake], 'lake pack "$archive"')

    def test_nothing_cleans_after_the_provider_build(self) -> None:
        for step in self.steps[self.index(self.NAME):]:
            for command in logical_commands(step.get("run") or ""):
                self.assertNotEqual(words(command)[:2], ["lake", "clean"], step.get("name"))

    def test_provider_module_sources_exist(self) -> None:
        if not (REPO_ROOT / "ZInQKernel").is_dir():
            self.skipTest("Lean sources are not checked out here")
        for module in sorted(set(PROVIDER_MODULES) | PSIDE_BUILT):
            path = module_source(module)
            self.assertTrue(path.is_file(), f"{module} has no source file {path}")

    def test_pside_targets_build_the_pside_provider_modules(self) -> None:
        if not (REPO_ROOT / "ZInQKernel").is_dir():
            self.skipTest("Lean sources are not checked out here")
        selected = [target[1:] for target in self.provider_command()[2:] if target.startswith("+" + PSIDE_PREFIX)]
        # A missing source raises here, so it fails rather than shrinking the closure.
        closure = import_closure(selected, read_module_imports, PSIDE_PREFIX)
        self.assertEqual(closure, set(PSIDE_BUILT))


class HeaderImportsTest(unittest.TestCase):
    def test_reads_only_the_header(self) -> None:
        text = (
            "/- Copyright notice\n"
            "   /- nested -/ still a comment\n"
            "   import Not.This -/\n"
            "-- a line comment\n"
            "module\n"
            "\n"
            "import A.B\n"
            "public import C.D  -- trailing comment\n"
            "import all E.F\n"
            "import G.H I.J\n"
            "\n"
            "/-! Module docs mention\n"
            "import K.L\n"
            "-/\n"
            "namespace X\n"
            "import M.N\n"
        )
        self.assertEqual(header_imports(text), ["A.B", "C.D", "E.F", "G.H", "I.J"])

    def test_no_header(self) -> None:
        self.assertEqual(header_imports("theorem t : True := trivial\nimport A\n"), [])

    def test_closure_follows_prefix_and_terminates_on_cycles(self) -> None:
        graph = {
            "P.Top": ["P.Mid", "Q.Outside"],
            "P.Mid": ["P.LeafA", "P.LeafB", "P.Top"],
            "P.LeafA": [],
            "P.LeafB": ["Mathlib.X"],
            "P.Unused": ["P.LeafA"],
        }
        self.assertEqual(import_closure(["P.Top"], graph.__getitem__, "P."),
                         {"P.Top", "P.Mid", "P.LeafA", "P.LeafB"})
        self.assertEqual(import_closure(["Q.Outside"], graph.__getitem__, "P."), set())

    def test_closure_reports_missing_sources(self) -> None:
        graph = {"P.Top": ["P.Gone"]}
        with self.assertRaises(KeyError):
            import_closure(["P.Top"], graph.__getitem__, "P.")

    def test_missing_module_file_raises(self) -> None:
        with self.assertRaises(FileNotFoundError):
            read_module_imports("ZInQKernel.Contrib.PSide.DoesNotExist")


class AuditStagesTest(WorkflowTestCase):
    NAME = "Audit every root-package declaration"

    def setUp(self) -> None:
        self.audit = self.commands(self.NAME)

    def test_fails_fast(self) -> None:
        self.assertEqual(self.step(self.NAME)["run"].style, "|")
        self.assertEqual(self.audit[0], "set -euo pipefail")

    def test_stages_keep_their_order(self) -> None:
        checks = [
            ("pack", lambda c: c == 'lake pack "$archive"'),
            ("policy", lambda c: c == 'policy="$(python3 .github/autoform_audit.py --policy blueprint)"'),
            ("assumptions probe", lambda c: "autoform work assumptions --help" in c and c.startswith("if uvx")),
            ("assumptions contract", lambda c: "autoform work assumptions blueprint --json" in c
             and c.endswith('> "$contract"')),
            ("old ref fallback", lambda c: "invalid choice: 'assumptions'" in c and '"$policy" != "allowed"' in c),
            ("open statements audit", lambda c: c.startswith("python3 .github/autoform_audit.py --open-statements")
             and c.endswith('"$AUTOFORM_ROOT_PACKAGE" "$archive" "$probe"')),
            ("targets audit", lambda c: c.startswith("python3 .github/autoform_audit.py --targets")
             and c.endswith('"$AUTOFORM_ROOT_PACKAGE" "$archive" "$probe"')),
            ("legacy audit", lambda c: c == 'python3 .github/autoform_audit.py "$AUTOFORM_ROOT_PACKAGE" '
             '"$archive" "$probe"'),
            ("lean path", lambda c: c == 'lean_path="$(lake env printenv LEAN_PATH)"'),
            ("probe run", lambda c: c == 'AUTOFORM_AUDIT_LEAN_PATH="$lean_path" LEAN_ABORT_ON_PANIC=1 '
             'lean "$probe" | tee "$output"'),
            ("success line", lambda c: c == "if ! tail -n 1 \"$output\" | grep -Eq "
             "'^kernel trust clean( except declared open statements)? \\('; then"),
        ]
        position = 0
        for what, predicate in checks:
            position = self.first_index(self.audit, predicate, what, position) + 1

    def stage_spans(self) -> dict[str, tuple[int, int]]:
        spans, open_label, opened = {}, None, 0
        for position, command in enumerate(self.audit):
            argv = words(command)
            if argv[:1] == ["stage_begin"]:
                self.assertIsNone(open_label, f"stage {argv[1:]} begins inside {open_label!r}")
                self.assertEqual(len(argv), 2)
                open_label, opened = argv[1], position
            elif command == "stage_end":
                self.assertIsNotNone(open_label, "stage_end without stage_begin")
                self.assertNotIn(open_label, spans)
                spans[open_label] = (opened, position)
                open_label = None
        self.assertIsNone(open_label, f"stage {open_label!r} never ends")
        return spans

    def test_timing_markers_wrap_each_stage(self) -> None:
        spans = self.stage_spans()
        self.assertEqual(list(spans), AUDIT_STAGES)
        expected_inside = {
            "lake pack": ['lake pack "$archive"'],
            "policy and assumptions extraction": ["autoform work assumptions --help",
                                                  "autoform work assumptions blueprint --json",
                                                  "--policy blueprint"],
            "archive parsing and probe generation": ["--open-statements", "--targets",
                                                     'autoform_audit.py "$AUTOFORM_ROOT_PACKAGE"'],
            "LEAN_PATH lookup": ["lake env printenv LEAN_PATH"],
            "axiom probe run": ['lean "$probe"'],
        }
        for label, needles in expected_inside.items():
            start, end = spans[label]
            inside = self.audit[start + 1:end]
            for needle in needles:
                self.assertTrue(any(needle in command for command in inside), f"{needle!r} is not in stage {label!r}")
        success = self.first_index(self.audit, lambda c: c.startswith("if ! tail -n 1"), "success check")
        self.assertGreater(success, spans["axiom probe run"][1])

    def test_timing_output_goes_to_stderr(self) -> None:
        markers = [c for c in self.audit if c.startswith('echo "[audit timing]')]
        self.assertGreaterEqual(len(markers), 2)
        for command in markers:
            self.assertTrue(command.endswith(">&2"), command)

    def test_trap_cleans_up_and_keeps_exit_status(self) -> None:
        traps = [words(c) for c in self.audit if words(c)[:1] == ["trap"]]
        self.assertEqual(len(traps), 1)
        trap = traps[0]
        self.assertEqual(trap[-1], "EXIT")
        body = trap[1]
        self.assertTrue(body.startswith("audit_status=$?;"), body)
        self.assertIn('rm -f "$archive" "$probe" "$contract" "$errors" "$output"', body)
        self.assertTrue(body.endswith('exit "$audit_status"'), body)

    def timing_snippet(self) -> str:
        lines = self.step(self.NAME)["run"].splitlines()
        start = next(i for i, line in enumerate(lines) if line.strip() == 'stage_label=""')
        end = next(i for i, line in enumerate(lines) if line.lstrip().startswith("trap '"))
        return "\n".join(lines[start:end + 1]) + "\n"

    def run_snippet(self, tail: str):
        bash = shutil.which("bash")
        if bash is None:
            self.skipTest("bash is not available")
        with tempfile.TemporaryDirectory() as tmp:
            names = ["archive", "probe", "contract", "errors", "output"]
            paths = [os.path.join(tmp, name) for name in names]
            for path in paths:
                Path(path).write_text("x", encoding="utf-8")
            prefix = "set -euo pipefail\n" + "".join(
                f"{name}={shlex.quote(path)}\n" for name, path in zip(names, paths))
            result = subprocess.run([bash, "-c", prefix + self.timing_snippet() + tail],
                                    capture_output=True, text=True, timeout=60, check=False)
            leftover = [path for path in paths if os.path.exists(path)]
        return result, leftover

    def test_timing_helpers_report_success(self) -> None:
        result, leftover = self.run_snippet('stage_begin "demo"\nstage_end\necho finished\n')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, "finished\n")
        self.assertIn("[audit timing] begin: demo", result.stderr)
        self.assertRegex(result.stderr, r"\[audit timing\] done: demo \(\d+s\)")
        self.assertNotIn("stopped in", result.stderr)
        self.assertEqual(leftover, [])

    def test_timing_helpers_propagate_failure(self) -> None:
        result, leftover = self.run_snippet('stage_begin "demo"\n(exit 3)\necho unreachable\n')
        self.assertEqual(result.returncode, 3)
        self.assertNotIn("unreachable", result.stdout)
        self.assertRegex(result.stderr, r"\[audit timing\] stopped in: demo \(\d+s, exit 3\)")
        self.assertEqual(leftover, [])

    def test_failed_pipeline_still_fails(self) -> None:
        result, leftover = self.run_snippet('stage_begin "demo"\nfalse | cat\nstage_end\n')
        self.assertEqual(result.returncode, 1)
        self.assertIn("stopped in: demo", result.stderr)
        self.assertEqual(leftover, [])


class CriticalGuardsTest(WorkflowTestCase):
    def test_triggers_permissions_and_pins(self) -> None:
        self.assertEqual(self.workflow["permissions"], {"contents": "read"})
        self.assertEqual(self.workflow["env"], {
            "AUTOFORM_SOURCE": "https://github.com/facebookresearch/autoform-bot.git",
            "AUTOFORM_REF": "46b46d6defaa19c618341e05c4cc0d819072a03d",
        })
        self.assertEqual(self.job["timeout-minutes"], "120")
        self.assertEqual(self.job["runs-on"], "ubuntu-latest")

    def test_actions_are_exactly_the_pinned_three(self) -> None:
        uses = [step["uses"] for step in self.steps if "uses" in step]
        self.assertEqual(uses, [CHECKOUT, SETUP_UV, UPLOAD])
        self.assertEqual(self.step("Install uv")["with"], {"version": "0.12.1"})
        for step in self.steps:
            self.assertFalse("uses" in step and "run" in step, step.get("name"))

    def test_blueprint_check_uses_pinned_autoform(self) -> None:
        self.assertEqual(self.step("Validate the theorem DAG")["run"],
                         'uvx --from "git+${AUTOFORM_SOURCE}@${AUTOFORM_REF}" autoform check blueprint')

    def test_elan_download_is_checksummed(self) -> None:
        commands = self.commands("Install elan")
        self.assertEqual(commands[0], "set -euo pipefail")
        self.assertIn("curl -sSfL https://github.com/leanprover/elan/releases/download/v4.2.3/"
                      "elan-x86_64-unknown-linux-gnu.tar.gz -o elan.tar.gz", commands)
        self.assertIn('echo "df0b2b3a439961ffcbb3985214365ffe40f49bc871df04dff268c7d8e21ca8b2  elan.tar.gz" '
                      "| sha256sum --check --strict", commands)
        self.assertIn("./elan-init -y --default-toolchain none", commands)

    def test_kernel_check_bypass_scan(self) -> None:
        commands = self.commands("Reject kernel-check bypass options")
        self.assertEqual(commands[0], "set -euo pipefail")
        # The token stays split in the workflow; this test keeps it split too.
        self.assertIn('forbidden="skip""KernelTC"', commands)
        self.assertIn("if matches=\"$(git grep -n -I \"$forbidden\" -- . ':!lean/README.md' "
                      "':!scripts/check_lean.py')\"; then", commands)
        self.assertIn('if [ "$grep_status" -ne 1 ]; then', commands)
        self.assertLess(self.index("Reject kernel-check bypass options"), self.index("Build Lean"))

    def test_cache_fetch_unchanged(self) -> None:
        self.assertEqual(self.step("Fetch the Mathlib build cache")["run"],
                         'lake exe cache get || echo "no cache available — building from source"')
        for step in self.steps:
            self.assertNotIn("cache", step.get("uses", ""))

    def test_default_build_unchanged(self) -> None:
        commands = self.commands("Build Lean")
        self.assertEqual(commands[0], "set -euo pipefail")
        position = 0
        for expected in [
            'lake translate-config toml "$evaluated_config"',
            'root_package="$(python3 .github/autoform_audit.py --root-package "$evaluated_config")"',
            'echo "AUTOFORM_ROOT_PACKAGE=$root_package" >> "$GITHUB_ENV"',
            "lake check-build",
            'lake clean "$root_package"',
            "lake build",
        ]:
            position = self.first_index(commands, lambda c, e=expected: c == e, expected, position) + 1
        self.assertNotIn("lake clean", commands, "bare lake clean would delete dependency caches")

    def test_review_policy_unchanged(self) -> None:
        commands = self.commands("Detect statement review")
        self.assertEqual(commands[0], "set -euo pipefail")
        self.assertIn('marker="blueprint/.autoform-review"', commands)
        self.assertIn('if [[ ! -f "$marker" || -L "$marker" ]] || '
                      '! echo "ad00ec55a215821b56f924782e25d7a77fff6696ee23cc465af20476b545b620  $marker" '
                      "| sha256sum --check --strict; then", commands)
        self.assertIn('echo "review cards or approvals exist without $marker" >&2', commands)
        verify = self.step("Verify statement reviews")
        self.assertEqual(verify["if"], "env.AUTOFORM_REVIEW_ENABLED == 'true'")
        self.assertEqual(verify["run"], 'uvx --from "git+${AUTOFORM_SOURCE}@${AUTOFORM_REF}" '
                                        "autoform review check blueprint --lean-root .")
        self.assertGreater(self.index("Detect statement review"), self.index("Audit every root-package declaration"))

    def test_upload_scope_unchanged_and_last(self) -> None:
        upload = self.steps[-1]
        self.assertEqual(upload["uses"], UPLOAD)
        self.assertEqual(upload["if"], "github.event_name == 'push'")
        self.assertEqual(upload["continue-on-error"], "true")
        self.assertEqual(upload["with"], {
            "name": "autoform-ileans",
            "path": ".lake/build/lib/lean/**/*.ilean",
            "include-hidden-files": "true",
        })

    def test_every_multiline_run_fails_fast(self) -> None:
        for step in self.steps:
            run = step.get("run")
            if isinstance(run, Block) and run.style == "|":
                self.assertEqual(logical_commands(run)[0], "set -euo pipefail", step.get("name"))

    def test_run_scripts_pass_bash_syntax_check(self) -> None:
        bash = shutil.which("bash")
        if bash is None:
            self.skipTest("bash is not available")
        for step in self.steps:
            run = step.get("run")
            if run:
                result = subprocess.run([bash, "-n", "-c", run], capture_output=True, text=True,
                                        timeout=30, check=False)
                self.assertEqual(result.returncode, 0, f"{step.get('name')}: {result.stderr}")


if __name__ == "__main__":
    unittest.main()
