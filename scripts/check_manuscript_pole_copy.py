#!/usr/bin/env python3
"""Derive the manuscript-pole copy of the kernel's pole-dependent modules, or check it.

The kernel's pinned headline is Route K: its pole curve is y^2 = x(x - l)(x + l).
The 5 November 2026 manuscript uses y^2 = x(x - l)(x + 3l) and takes pole
completeness (its Theorem 5.2) as the pole input. That second result lives in
ZInQKernel/Contrib/ManuscriptPole/, in the Lean namespace `ManuscriptPole`, and is
a derived copy: this program rebuilds it from the Route K sources and one patch
(scripts/manuscript_pole_copy/route.patch). No Route K file is opened for writing.

Without --write nothing is written: the tracked copy is compared with a fresh
derivation, and any difference, missing file or stale file is an error. A pass
says the copy is current. It says nothing about whether the copy compiles; the
kernel build compiles every module under ZInQKernel/Contrib/.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
PATCH = "scripts/manuscript_pole_copy/route.patch"
KERNEL = "ZInQKernel/"
CONTRIB = "ZInQKernel/Contrib/"
COPY_DIR = "ZInQKernel/Contrib/ManuscriptPole/"
COPY_PREFIX = "ZInQKernel.Contrib.ManuscriptPole."
NAMESPACE = "ManuscriptPole"
# The two modules whose theorems are the second result. The copy is everything they
# import that depends on a patched module.
HEADLINES = ("ZInQKernel.Main", "ZInQKernel.MainGreenTao")
STATEMENT = COPY_DIR + "Statement.lean"
HEADLINE_THEOREM = ("ZInQ.exists_bounded_integer_polynomial_defining_integers_of_"
                    "sixContactMin_poleCompleteness")

IMPORT = re.compile(r"^import\s+(\S+)\s*$")
DECLARATION = (r"(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec)\s+)*"
               r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque)\s+")
ROOT_DECLARATION = re.compile(r"^(\s*" + DECLARATION + r")_root_\.(?=[A-Za-z_])")


class CopyError(ValueError):
    pass


def git(root, *args):
    return subprocess.run(["git", "-c", "safe.directory=" + str(root.resolve()), "-C", str(root), *args],
                          check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout


def tracked(root):
    return [p.decode("utf-8") for p in git(root, "ls-files", "-z").split(b"\0") if p]


def module_of(path):
    return path[:-5].replace("/", ".")


def path_of(module):
    return module.replace(".", "/") + ".lean"


def copy_path(path):
    return COPY_DIR + path[len(KERNEL):]


# --- the patch -----------------------------------------------------------------

def parse_patch(text):
    """Unified diff -> {path: [(old_lines, new_lines), ...]}. Line numbers are ignored."""
    hunks, path, old, new, want_old, want_new = {}, None, None, None, 0, 0
    lines = text.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    for number, line in enumerate(lines, 1):
        if want_old or want_new:
            # Inside a hunk the counts of its header decide, so a removed Lean comment
            # (`--- text`) is never read as a file header.
            tag = line[:1] or " "     # an editor may strip the space of an empty context line
            if tag not in (" ", "-", "+"):
                raise CopyError(f"{PATCH}:{number}: not a unified diff line: {line[:60]!r}")
            if tag != "+":
                old.append(line[1:])
                want_old -= 1
            if tag != "-":
                new.append(line[1:])
                want_new -= 1
            if want_old < 0 or want_new < 0:
                raise CopyError(f"{PATCH}:{number}: hunk longer than its header says")
        elif line.startswith(("diff --git ", "index ", "#")):
            continue          # git's own headers, and `#` notes between sections
        elif line.startswith("--- "):
            if not line.startswith("--- a/"):
                raise CopyError(f"{PATCH}:{number}: the patch may only modify existing files")
            path = None
        elif line.startswith("+++ "):
            if not line.startswith("+++ b/"):
                raise CopyError(f"{PATCH}:{number}: the patch may only modify existing files")
            path = line[6:]
            if path in hunks:
                raise CopyError(f"{PATCH}:{number}: second section for {path}")
            hunks[path] = []
        elif match := re.match(r"^@@ -\d+(?:,(\d+))? \+\d+(?:,(\d+))? @@", line):
            if path is None:
                raise CopyError(f"{PATCH}:{number}: hunk before a file header")
            want_old = int(match.group(1)) if match.group(1) is not None else 1
            want_new = int(match.group(2)) if match.group(2) is not None else 1
            old, new = [], []
            hunks[path].append((old, new))
        else:
            raise CopyError(f"{PATCH}:{number}: not a unified diff line: {line[:60]!r}")
    if want_old or want_new:
        raise CopyError(f"{PATCH}: the last hunk is shorter than its header says")
    for path, items in hunks.items():
        if not items or any(old == new for old, new in items):
            raise CopyError(f"{PATCH}: empty section or no-op hunk for {path}")
    return hunks


def apply_hunks(path, text, hunks):
    """Apply every hunk where its old lines occur, in order; each must occur exactly once."""
    lines = text.split("\n")
    cursor = 0
    for index, (old, new) in enumerate(hunks, 1):
        if not old:
            raise CopyError(f"{PATCH}: hunk {index} for {path} has no context")
        found = [i for i in range(len(lines) - len(old) + 1) if lines[i:i + len(old)] == old]
        if len(found) != 1 or found[0] < cursor:
            raise CopyError(f"{PATCH}: hunk {index} for {path} no longer applies "
                            f"({len(found)} matches). The Route K source changed here: "
                            "review the change and update the patch.")
        lines[found[0]:found[0] + len(old)] = new
        cursor = found[0] + len(new)
    return "\n".join(lines)


# --- reading Lean source --------------------------------------------------------

def code_lines(text):
    """For each line: (starts_in_code, the line with comments and string contents blanked)."""
    result, depth, in_string = [], 0, False
    for line in text.split("\n"):
        starts_in_code = depth == 0 and not in_string
        out, i = [], 0
        while i < len(line):
            two = line[i:i + 2]
            if in_string:
                if line[i] == "\\":
                    i += 2
                    continue
                if line[i] == '"':
                    in_string = False
                    out.append('"')
                i += 1
            elif depth:
                if two == "/-":
                    depth, i = depth + 1, i + 2
                elif two == "-/":
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            elif two == "/-":
                depth, i = 1, i + 2
            elif two == "--":
                break
            elif line[i] == '"':
                in_string = True
                out.append('"')
                i += 1
            else:
                out.append(line[i])
                i += 1
        result.append((starts_in_code, "".join(out)))
    if depth or in_string:
        raise CopyError("unterminated comment or string")
    return result


def imports_of(text):
    return [m.group(1) for code_start, code in code_lines(text)
            if code_start and (m := IMPORT.match(code))]


def prefixes(name):
    parts = name.split(".")
    return [".".join(parts[:i]) for i in range(1, len(parts) + 1)]


def rewrite_open(code, line, registered):
    """`open ZInQ.X` inside the wrapper would mean the copy's `ZInQ.X` alone. Open the kernel's too.

    Lean resolves `ZInQ.X` there to `ManuscriptPole.ZInQ.X` when a copied module declares that
    namespace, and then does not open the kernel's `ZInQ.X`. The copy needs both: its own
    declarations and those of the unchanged kernel modules. So `open ZInQ.X` becomes
    `open ZInQ.X _root_.ZInQ.X`. The first name must stay as written: it is the copy's namespace
    when that exists and the kernel's otherwise, and naming the copy's outright would fail
    whenever no copied module declares it.
    """
    match = re.match(r"^(\s*open\s+)(.*?)(\s+in)?\s*$", code)
    if not match or code.rstrip() != line.rstrip():
        return line          # a trailing comment or a form this program does not rewrite
    names = match.group(2).split()
    if (not names or not all(re.fullmatch(r"[A-Za-z_][\w.'!?]*", n) for n in names)
            or {"hiding", "renaming", "scoped", "in"}.intersection(names)):
        return line          # `open N (a b)`, `hiding`, `renaming`, `scoped`: left as written
    out = []
    for name in names:
        out.append(name)
        if name == "ZInQ" or name.startswith("ZInQ."):
            out.append("_root_." + name)
            registered.append(name)
    return match.group(1) + " ".join(out) + (match.group(3) or "")


def transform(path, text, copied, notice):
    """One kernel module (already patched) -> its copy in the namespace `ManuscriptPole`."""
    if not text.endswith("\n"):
        raise CopyError(f"{path}: no final newline")
    lines = text[:-1].split("\n")
    code = code_lines(text[:-1])
    last_import = -1
    for i, (code_start, stripped) in enumerate(code):
        if code_start and IMPORT.match(stripped):
            last_import = i
    if last_import < 0:
        raise CopyError(f"{path}: no import line")
    head, body, registered = [], [], []
    for i in range(last_import + 1):
        match = IMPORT.match(code[i][1]) if code[i][0] else None
        if match and match.group(1) in copied:
            head.append("import " + COPY_PREFIX + match.group(1)[len("ZInQKernel."):])
        elif code[i][0] and code[i][1].strip() and not match:
            raise CopyError(f"{path}:{i + 1}: a command before the last import")
        else:
            head.append(lines[i])
    stack = []            # ("namespace", written name) | ("section", name) | ("mutual", "")
    for i in range(last_import + 1, len(lines)):
        line = lines[i]
        code_start, stripped = code[i]
        if not code_start:
            body.append(line)
            continue
        if IMPORT.match(stripped):
            raise CopyError(f"{path}:{i + 1}: import after the header")
        if "_root_" in re.sub(r"[A-Za-z0-9']_root_|_root_[A-Za-z0-9_']", "", stripped):
            if not ROOT_DECLARATION.match(stripped) or stripped.count("_root_.") != 1:
                raise CopyError(f"{path}:{i + 1}: `_root_` outside a declaration name is not supported")
            line = ROOT_DECLARATION.sub(lambda m: m.group(1) + "_root_." + NAMESPACE + ".", line, count=1)
        match = re.match(r"^\s*namespace\s+(\S+)\s*$", stripped)
        if match:
            before = ".".join(name for kind, name in stack if kind == "namespace")
            full = (before + "." if before else "") + match.group(1)
            if full.split(".")[0] != "ZInQ":
                raise CopyError(f"{path}:{i + 1}: namespace {full} is outside ZInQ")
            stack.append(("namespace", match.group(1)))
            registered.append(full)
            fresh = [p for p in prefixes(full) if p not in prefixes(before)] if before else prefixes(full)
            body.append(line)
            body.append("open " + " ".join("_root_." + p for p in fresh))
            continue
        match = re.match(r"^\s*(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$", stripped)
        if match:
            stack.append(("section", match.group(1) or ""))
        elif re.match(r"^\s*mutual\s*$", stripped):
            stack.append(("mutual", ""))
        else:
            match = re.match(r"^\s*end(?:\s+(\S+))?\s*$", stripped)
            if match:
                if not stack or (stack[-1][0] != "mutual" and stack[-1][1] != (match.group(1) or "")):
                    raise CopyError(f"{path}:{i + 1}: unbalanced `end`")
                stack.pop()
            elif re.match(r"^\s*open\s", stripped):
                line = rewrite_open(stripped, line, registered)
        body.append(line)
    if stack:
        raise CopyError(f"{path}: unclosed {stack[-1][0]} {stack[-1][1]}")
    return "\n".join(
        [notice] + head +
        ["", "-- Every kernel namespace opened below exists, whether or not an import declares it."] +
        [f"namespace {name} end {name}" for name in dict.fromkeys(registered)] +
        ["", "namespace " + NAMESPACE, "open " + NAMESPACE,
         "-- `open ZInQ.X` is written `open ZInQ.X _root_.ZInQ.X` here, so the kernel's namespace is",
         "-- opened beside the copy's and the linter's warning about the first name does not apply.",
         "set_option linter.ambiguousOpen false"] +
        body +
        ["", "end " + NAMESPACE, ""])


def statement():
    """The second result, stated once with every name written in full."""
    return f"""/- GENERATED by scripts/check_manuscript_pole_copy.py. Do not edit. -/
import {COPY_PREFIX}MainGreenTao

/-!
# The manuscript's pole route: the statement of the second result

The kernel's pinned headline is Route K (`ZInQ.Contract.expectedHeadline`,
`ZInQKernel/Contract.lean`); this file does not change it. Beside it, the modules of
`ZInQKernel/Contrib/ManuscriptPole/` prove the same frozen target by the route of the 11/5
manuscript, whose pole curve is `y² = x(x - ℓ)(x + 3ℓ)` and whose pole input is pole completeness
(the manuscript's Theorem 5.2).

In the type below, `ZInQ.SixContactMin` and `ZInQ.FrozenTarget` are the kernel's own declarations,
the ones the Route K headline uses. Only `ManuscriptPole.ZInQ.PoleCompleteness` belongs to the copy:
it is Theorem 5.2 for the manuscript's pole polynomial `ManuscriptPole.ZInQ.polePoly`
(`ZInQKernel/Contrib/ManuscriptPole/Hypotheses/Pole.lean`). This theorem checks that complete
type, with no further premise. It does not discharge either premise.
-/

theorem {NAMESPACE}.expectedHeadline :
    _root_.ZInQ.SixContactMin →
    _root_.{NAMESPACE}.ZInQ.PoleCompleteness →
    _root_.ZInQ.FrozenTarget :=
  @_root_.{NAMESPACE}.{HEADLINE_THEOREM}
"""


# --- the derivation ------------------------------------------------------------

def derive(sources, patch_text):
    """sources: {path: text} of the kernel's Lean modules -> ({copy path: text}, report)."""
    hunks = parse_patch(patch_text)
    modules = {}
    for path, text in sources.items():
        if path.startswith(CONTRIB) or not path.startswith(KERNEL) or not path.endswith(".lean"):
            continue
        modules[module_of(path)] = text
    for path, items in hunks.items():
        if module_of(path) not in modules or not path.startswith(KERNEL) or path.startswith(CONTRIB):
            raise CopyError(f"{PATCH}: {path} is not a kernel module outside Contrib")
        modules[module_of(path)] = apply_hunks(path, modules[module_of(path)], items)
    patched = {module_of(path) for path in hunks}
    imports = {m: [i for i in imports_of(text) if i in modules] for m, text in modules.items()}
    for headline in HEADLINES:
        if headline not in modules:
            raise CopyError("missing headline module " + headline)
    reach, todo = set(HEADLINES), list(HEADLINES)
    while todo:
        for dep in imports[todo.pop()]:
            if dep not in reach:
                reach.add(dep)
                todo.append(dep)
    # Depends on a patched module: least fixed point over the modules the headlines import.
    copied = {m for m in reach if m in patched}
    changed = True
    while changed:
        changed = False
        for m in reach - copied:
            if any(dep in copied for dep in imports[m]):
                copied.add(m)
                changed = True
    unused = sorted(patched - copied)
    if unused:
        raise CopyError("patched but not imported by a headline: " + ", ".join(unused))
    output = {}
    for module in sorted(copied):
        path = path_of(module)
        source = "Source: " + path + (" with " + PATCH if module in patched else ", unchanged")
        notice = ("/- GENERATED by scripts/check_manuscript_pole_copy.py. Do not edit. " + source +
                  ".\n   The manuscript's pole route, stated beside Route K; see Statement.lean here. -/")
        output[copy_path(path)] = transform(path, modules[module], copied, notice)
    if STATEMENT in output:
        raise CopyError("a kernel module is named like the generated statement file")
    output[STATEMENT] = statement()
    report = {"schema": "manuscript-pole-copy/v1",
              "patch_sha256": hashlib.sha256(patch_text.encode("utf-8")).hexdigest(),
              "patched": sorted(patched), "modules": sorted(copied),
              "files": len(output), "namespace": NAMESPACE, "module_prefix": COPY_PREFIX[:-1]}
    return output, report


def read_sources(root):
    sources = {}
    for path in tracked(root):
        if path.startswith(KERNEL) and path.endswith(".lean") and not path.startswith(CONTRIB):
            sources[path] = (root / path).read_bytes().decode("utf-8")
    return sources


def compare(root, output):
    """Problems of the tracked copy against the derivation; empty when it is current."""
    problems = []
    present = {p for p in tracked(root) if p.startswith(COPY_DIR)}
    on_disk = {p.relative_to(root).as_posix() for p in (root / COPY_DIR).rglob("*") if p.is_file()} \
        if (root / COPY_DIR).is_dir() else set()
    for path in sorted(output):
        full = root / path
        if not full.is_file():
            problems.append("missing: " + path)
        elif full.read_bytes() != output[path].encode("utf-8"):
            problems.append("differs from its derivation: " + path)
        elif path not in present:
            problems.append("not tracked by git: " + path)
    for path in sorted((present | on_disk) - set(output)):
        problems.append("stale, no source derives it: " + path)
    return problems


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--write", action="store_true",
                        help="write the derived copy instead of comparing it")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args(argv)
    root = args.root.resolve()
    # The kernel sources are byte-exact in git; the patch is ordinary text and may be checked out
    # with CRLF line ends.
    patch_text = (root / PATCH).read_bytes().decode("utf-8").replace("\r\n", "\n")
    output, report = derive(read_sources(root), patch_text)
    if args.write:
        for path, text in output.items():
            full = root / path
            full.parent.mkdir(parents=True, exist_ok=True)
            if not full.is_file() or full.read_bytes() != text.encode("utf-8"):
                full.write_bytes(text.encode("utf-8"))
        # A stale file is reported, never removed: deleting is the maintainer's decision.
        problems = [p for p in compare(root, output) if p.startswith("stale")]
    else:
        problems = compare(root, output)
    report["status"] = "current" if not problems else "drifted"
    report["problems"] = problems
    raw = json.dumps(report, indent=2) + "\n"
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(raw, encoding="utf-8")
    print(raw, end="")
    if problems:
        raise CopyError("the copy is not its derivation (" + str(len(problems)) + " problems); "
                        "run with --write and review the diff")


if __name__ == "__main__":
    try:
        main()
    except (CopyError, OSError, KeyError, UnicodeDecodeError, subprocess.CalledProcessError) as error:
        print("Manuscript pole copy rejected: " + str(error), file=sys.stderr)
        sys.exit(1)
