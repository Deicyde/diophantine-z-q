#!/usr/bin/env python3
"""Check that a Lean file's code (comments and docstrings stripped) is unchanged.

Usage: check_code_unchanged.py [--rev REV] FILE [FILE ...]

For each FILE, compares the working-tree version with `git show REV:FILE`
(default REV = 6988c7fe, the base of task loc-adopt) after removing
  * nested block comments `/- ... -/`, including docstrings `/-- -/` and `/-! -/`,
  * line comments `-- ...`,
outside string and character literals, and normalizing whitespace
(each token sequence split on whitespace). Prints IDENTICAL or a unified diff
of the stripped token lines. Exit code 0 if all files are identical, 1 otherwise.
"""
import argparse
import difflib
import subprocess
import sys


def strip_comments(src: str) -> str:
    out = []
    i, n = 0, len(src)
    depth = 0
    while i < n:
        if depth > 0:
            if src.startswith("/-", i):
                depth += 1
                i += 2
            elif src.startswith("-/", i):
                depth -= 1
                i += 2
                if depth == 0:
                    out.append(" ")
            else:
                i += 1
            continue
        c = src[i]
        if src.startswith("/-", i):
            depth = 1
            i += 2
        elif src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
        elif c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append(src[i:j + 1])
            i = j + 1
        elif c == "'" and i + 2 < n and (src[i + 2] == "'" or (src[i + 1] == "\\" and i + 3 < n and src[i + 3] == "'")):
            # character literal 'x' or '\x'
            k = i + 3 if src[i + 2] == "'" else i + 4
            out.append(src[i:k])
            i = k
        else:
            out.append(c)
            i += 1
    if depth != 0:
        raise ValueError("unterminated block comment")
    return "".join(out)


def normalize(src: str) -> list:
    lines = []
    for line in strip_comments(src).splitlines():
        toks = line.split()
        if toks:
            lines.append(" ".join(toks))
    return lines


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--rev", default="6988c7fe")
    ap.add_argument("files", nargs="+")
    a = ap.parse_args()
    ok = True
    for f in a.files:
        old = subprocess.run(["git", "show", f"{a.rev}:{f}"], check=True,
                             capture_output=True, text=True).stdout
        new = open(f, encoding="utf-8").read()
        o, w = normalize(old), normalize(new)
        if o == w:
            print(f"IDENTICAL {f} (rev {a.rev}; {len(w)} code lines; "
                  f"raw files {'equal' if old == new else 'differ in comments only'})")
        else:
            ok = False
            print(f"DIFFERENT {f} (rev {a.rev})")
            sys.stdout.writelines(difflib.unified_diff(
                [l + "\n" for l in o], [l + "\n" for l in w], f"{a.rev}:{f}", f))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
