"""Shortest import path from the H roots to each target module (BFS over the import graph)."""
import json, sys, collections
g = json.load(open(sys.argv[1])); imp = g['imp']
roots = [m for m in imp if m.startswith(('ZInQKernel.OneProof.H.', 'ZInQKernel.HDecomp.'))]
par = {r: None for r in roots}; q = collections.deque(sorted(roots))
while q:
    m = q.popleft()
    for b in imp.get(m, []):
        if b not in par: par[b] = m; q.append(b)
for t in sys.argv[2:]:
    p = []; x = t
    while x is not None: p.append(x); x = par.get(x, None) if x in par else None
    print(' <- '.join(p) if t in par else t + ': not reached')
