"""List, in topological order, the modules of Main's import closure that import (transitively) a patched module."""
import re, sys, os
root = sys.argv[1]; top = sys.argv[2]; patched = set(sys.argv[3].split(','))
def path(m): return os.path.join(root, *m.split('.')) + '.lean'
imps = {}
def load(m):
    if m in imps: return
    p = path(m)
    if not os.path.exists(p): imps[m] = []; return
    src = open(p).read()
    imps[m] = [x for x in re.findall(r'^import\s+(\S+)', src, re.M) if x.startswith('ZInQKernel')]
    for x in imps[m]: load(x)
load(top)
order, seen = [], set()
def topo(m):
    if m in seen: return
    seen.add(m)
    for x in imps[m]: topo(x)
    order.append(m)
topo(top)
down = set(patched)
for m in order:
    if any(x in down for x in imps[m]): down.add(m)
for m in order:
    if m in down: print(m)
