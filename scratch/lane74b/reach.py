"""H-reach of the Route K tree: which RouteK modules the H chain (OneProof/H/**, HDecomp/**) and the
headline (OneProof/Main) import, and the edges into RouteK from outside it."""
import json, sys
g = json.load(open(sys.argv[1])); imp = g['imp']
pref = sys.argv[2] if len(sys.argv) > 2 else 'ZInQKernel.RouteK'
roots = [m for m in imp if m.startswith(('ZInQKernel.OneProof.H.', 'ZInQKernel.HDecomp.'))] + ['ZInQKernel.OneProof.Main']
def closure(rs):
    seen, st = set(), list(rs)
    while st:
        m = st.pop()
        if m in seen or m not in imp: continue
        seen.add(m); st += imp[m]
    return seen
reach = closure(roots)
rk = sorted(m for m in reach if m.startswith(pref))
print('H+Main reach:', len(reach), pref, 'in reach:', len(rk))
for m in rk: print('  ', m)
print('edges into', pref, 'from outside it (importer in reach):')
for a in sorted(reach):
    if a.startswith(pref): continue
    for b in imp[a]:
        if b.startswith(pref): print('  ', a, '->', b)
