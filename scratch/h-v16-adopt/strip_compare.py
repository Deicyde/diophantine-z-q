"""Strip Lean comments/docstrings (nested /- -/ and --) from two files and compare the code."""
import sys

def strip(src):
    out, i, depth, n = [], 0, 0, len(src)
    in_str = False
    while i < n:
        if depth == 0 and not in_str and src.startswith('--', i):
            j = src.find('\n', i); i = n if j < 0 else j; continue
        if not in_str and src.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth > 0 and src.startswith('-/', i):
            depth -= 1; i += 2; continue
        if depth > 0:
            i += 1; continue
        c = src[i]
        if c == '"' and (i == 0 or src[i-1] != '\\'):
            in_str = not in_str
        out.append(c); i += 1
    return '\n'.join(l.rstrip() for l in ''.join(out).split('\n') if l.strip())

a, b = (strip(open(p, encoding='utf-8').read()) for p in sys.argv[1:3])
print('code identical' if a == b else 'CODE DIFFERS')
