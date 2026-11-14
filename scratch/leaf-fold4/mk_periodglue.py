#!/usr/bin/env python3
"""leaf-fold4: part partsF/c90_periodglue.lean = period-map's parts and period-glue's six files over the chain.
period-glue's PGAll.lean is PGBase (fibre-qm-period's FibreQM.lean 1-20634 + part_fqm = this chain's LPrefix ...
a80_fqm) + period-map's part_light, part_theta, part_siegel, part_order, part_heavy + period-glue's BCU,
QMTwist, PiTwist, S8, W8, SFA, final_part. This part is those files in that order (import, #print, #check
lines dropped), with each declaration whose full name already occurs in the chain (LPrefix, parts/,
partsF/c1*-c8*) or earlier in this part dropped (as mk_propts.py does), and leaf-fold's HDec edits (mk_lf3.hdec).
Run from scratch/leaf-fold4."""
import sys, re, glob
sys.path.insert(0, 'py')
from chunks import chunks, text, fullnames
sys.path.insert(0, '.')
from mk_lf3 import hdec  # noqa
import mk_propts_walk as W
R = '../'
seen = {}
for f in ['olean/LPrefix.lean'] + sorted(glob.glob('parts/*.lean')) + sorted(glob.glob('partsF/c[1-8]*.lean')):
    for n, c in fullnames(chunks(open(f).read())):
        if isinstance(n, str) and n.startswith('HDec.'): n = n[5:]
        if isinstance(n, tuple) and n[1].startswith('HDec'): n = (n[0], n[1][5:], n[2])
        seen.setdefault(n, text(c))
W.seen_text = set(seen.values())
W.TEXT_DEDUP = False
parts = []
OPENLP = 'open ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)'
srcs = ['period-map/part_light.lean', 'period-map/part_theta.lean', 'period-map/part_siegel.lean',
        'period-map/part_order.lean', 'period-map/part_heavy.lean',
        'period-glue/BCU.lean', 'period-glue/QMTwist.lean', 'period-glue/PiTwist.lean', 'period-glue/S8.lean',
        'period-glue/W8.lean', 'period-glue/SFA.lean', 'period-glue/final_part.lean']
for f in srcs:
    s = open(R + f).read()
    s = '\n'.join(l for l in s.split('\n') if not (l.startswith('import ') or l.startswith('#print') or l.startswith('#check')))
    # the chain's a80_fqm opens leaf-push2's analytic names explicitly (g0-assemble2's port); FibreQM.lean had
    # copies of them in HSyn.G0Split: the same `open` after each `namespace HSyn.G0Split.FibreQM…` line
    s = re.sub(r'^(namespace HSyn\.G0Split\.FibreQM\S*)$', r'\1\n' + OPENLP, s, flags=re.M)
    t, d = W.walk(chunks(s), seen, tag=f)
    parts.append('/-! ## leaf-fold4: scratch/%s (declarations already in the chain dropped) -/\n\n' % f + t)
hdr = ('-- (leaf-fold4) mk_periodglue.py: period-map parts light/theta/siegel/order/heavy and period-glue BCU, QMTwist,\n'
       '-- PiTwist, S8, W8, SFA, final_part (import/#print lines dropped; declarations already in the chain dropped)\n')
open('partsF/c90_periodglue.lean', 'w').write(hdr + hdec('\n\n'.join(parts)).replace('_root_.PeriodGlue.', '_root_.HDec.PeriodGlue.') + '\n')
print('ok')
