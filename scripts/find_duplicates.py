#!/usr/bin/env python3
"""List likely duplicate declarations in ZInQKernel/ (a text-level scan, no Lean needed).

1. Short names declared as theorems or lemmas in more than one namespace.
2. Theorems with the same statement (binders and type, whitespace-normalized) under
   different names.

Usage: python3 scripts/find_duplicates.py [ROOT]   (default ROOT = ZInQKernel)
"""
import os
import re
import sys
from collections import defaultdict

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*"
    r"(theorem|lemma)\s+([^\s(\[{:]+)")


def strip_comments(text):
    text = re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def statement(lines, i, start):
    """The text after the name up to the `:=` (or `|`, `where`) that ends the statement."""
    buf = lines[i][start:]
    j = i
    while True:
        depth = 0
        for k, ch in enumerate(buf):
            if ch in "([{⟨":
                depth += 1
            elif ch in ")]}⟩":
                depth -= 1
            elif depth == 0 and buf.startswith(":=", k):
                return " ".join(buf[:k].split())
        j += 1
        if j >= len(lines) or j - i > 60:
            return None
        buf += " " + lines[j]


def scan(root):
    decls = []
    for d, _, fs in os.walk(root):
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            path = os.path.join(d, f)
            lines = strip_comments(open(path, encoding="utf-8").read()).split("\n")
            stack = []  # entries: ("ns", name) or ("sec", name)
            for i, line in enumerate(lines):
                s = line.strip()
                m = re.match(r"^namespace\s+(\S+)", s)
                if m:
                    stack.append(("ns", m.group(1)))
                    continue
                m = re.match(r"^(?:noncomputable\s+)?section(?:\s+(\S+))?", s)
                if m and not s.startswith("section_"):
                    stack.append(("sec", m.group(1) or ""))
                    continue
                m = re.match(r"^end(?:\s+(\S+))?\s*$", s)
                if m and stack:
                    stack.pop()
                    continue
                m = DECL.match(s)
                if m:
                    name = m.group(2)
                    ns = ".".join(n for k, n in stack if k == "ns")
                    full = name[1:] if name.startswith("_root_.") else (
                        f"{ns}.{name}" if ns else name)
                    stmt = statement(lines, i, line.index(name) + len(name))
                    decls.append((full, path, i + 1, stmt))
    return decls


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else "ZInQKernel"
    decls = scan(root)
    by_short = defaultdict(list)
    for full, path, line, _ in decls:
        by_short[full.rsplit(".", 1)[-1]].append((full, path, line))
    by_full = defaultdict(list)
    for full, path, line, _ in decls:
        by_full[full].append((path, line))
    print("## Full names declared in more than one place\n")
    for full, occ in sorted(by_full.items()):
        if len(occ) > 1:
            print(full)
            for path, line in occ:
                print(f"    {path}:{line}")
    print("\n## Short names declared in more than one namespace\n")
    for short, occ in sorted(by_short.items()):
        if len({o[0] for o in occ}) > 1:
            print(short)
            for full, path, line in occ:
                print(f"    {full}  ({path}:{line})")
    by_stmt = defaultdict(list)
    for full, path, line, stmt in decls:
        if stmt and len(stmt) > 25:
            by_stmt[stmt].append((full, path, line))
    print("\n## Identical statements under different names\n")
    for stmt, occ in sorted(by_stmt.items(), key=lambda kv: kv[1][0][1]):
        if len({o[0] for o in occ}) > 1:
            print(stmt[:200])
            for full, path, line in occ:
                print(f"    {full}  ({path}:{line})")


if __name__ == "__main__":
    main()
