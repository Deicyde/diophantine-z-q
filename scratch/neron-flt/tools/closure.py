import sys, os, re
root = os.path.expanduser('~/flt-src')
def path(m): return os.path.join(root, m.replace('.', '/') + '.lean')
def imports(m):
    p = path(m)
    if not os.path.exists(p): return None
    out = []
    for line in open(p, encoding='utf-8'):
        s = line.strip()
        if s.startswith('import '):
            out += s.split()[1:]
        elif s and not s.startswith('--') and not s.startswith('/-') and not s.startswith('module') and not s.startswith('public'):
            if not s.startswith('import'): break
    return out
start = sys.argv[1]
seen = {}; stack = [start]
while stack:
    m = stack.pop()
    if m in seen: continue
    im = imports(m)
    if im is None: continue  # external (Mathlib)
    seen[m] = im
    stack += im
for m in sorted(seen): print(m)
