"""nsat.py FILE LINE...: print the namespace/section stack at each LINE (comment-aware)."""
import re, sys, pathlib
src = open(pathlib.Path(__file__).parent / 'del_decls.py').read()
exec(src[src.index('def in_comment'):src.index('def main')])
lines = open(sys.argv[1]).read().split('\n'); inc = in_comment(lines)
want = sorted(int(x) for x in sys.argv[2:]); stack = []
for i, l in enumerate(lines, 1):
    while want and want[0] == i: print(i, '.'.join(n for k, n in stack if k == 'ns'), '|', ' '.join(f'{k}:{n}' for k, n in stack)); want.pop(0)
    if inc[i - 1]: continue
    m = re.match(r'^namespace\s+(\S+)', l)
    if m: stack.append(('ns', m.group(1))); continue
    m = re.match(r'^(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$', l)
    if m: stack.append(('sec', m.group(1) or '')); continue
    if re.match(r'^end(?:\s+(\S+))?\s*$', l) and stack: stack.pop()
