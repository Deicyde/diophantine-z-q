"""Check that only comments/docstrings changed in Lean files between two commits.

Usage: python3 strip_check.py BASE [HEAD]. Strips `--` line comments and nested `/- ... -/` block
comments (including `/--` docstrings and `/-!` module docs), respecting string literals and char
literals, then compares the stripped old and new texts of every changed .lean file.
"""
import subprocess, sys

def strip(src):
    out = []; i = 0; n = len(src); depth = 0
    while i < n:
        if depth:
            if src.startswith('/-', i): depth += 1; i += 2
            elif src.startswith('-/', i): depth -= 1; i += 2
            else: i += 1
            continue
        c = src[i]
        if src.startswith('/-', i): depth = 1; i += 2; continue
        if src.startswith('--', i):
            j = src.find('\n', i); i = n if j < 0 else j; continue
        if c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            out.append(src[i:j + 1]); i = j + 1; continue
        if c == "'" and i + 2 < n and (src[i + 2] == "'" or (src[i + 1] == '\\' and src[i + 3] == "'")):
            k = i + (3 if src[i + 2] == "'" else 4)
            out.append(src[i:k]); i = k; continue
        out.append(c); i += 1
    return ''.join(out)

def show(rev, path):
    return subprocess.run(['git', 'show', f'{rev}:{path}'], capture_output=True, text=True,
                          check=True).stdout

base = sys.argv[1]; head = sys.argv[2] if len(sys.argv) > 2 else 'HEAD'
files = subprocess.run(['git', 'diff', '--name-only', base, head, '--', '*.lean'],
                       capture_output=True, text=True, check=True).stdout.split()
ok = True
for f in files:
    a, b = strip(show(base, f)), strip(show(head, f))
    same = a == b
    ok &= same
    print(f"{'IDENTICAL' if same else 'DIFFERENT'}  {f}")
print('ALL IDENTICAL' if ok and files else ('NO LEAN FILES CHANGED' if not files else 'MISMATCH'))
sys.exit(0 if ok else 1)
