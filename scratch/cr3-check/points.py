"""Step 4: for every (d, a) with the CR3 hypothesis true in Lean (cmp40.json), find a rational point
on C_d with x != 0 and x/a a square: P = G + T for a non-torsion point G returned by PARI ellrank
(increasing effort, each try under a PARI alarm) or ellheegner (small d), and T in E[2]. Every point
is rechecked with exact rational arithmetic (Fraction): y^2 = x^3 - d^2 x and x/a a square.
Usage: python points.py cmp40.json TLIM SHARD NSHARDS  -> points40_SHARD.json"""
import json, sys
from fractions import Fraction as Fr
from math import isqrt
import cypari2
pari = cypari2.Pari()
pari.allocatemem(2 * 10**9)


def is_sq_rat(r):
    r = Fr(r)
    if r < 0: return False
    n, m = r.numerator, r.denominator
    return isqrt(n) ** 2 == n and isqrt(m) ** 2 == m


def to_fr(z):
    return Fr(int(pari.numerator(z)), int(pari.denominator(z)))


TLIM = int(sys.argv[2])
SHARD, NSH = int(sys.argv[3]), int(sys.argv[4])
rows = json.load(open(sys.argv[1]))
rows = [r for r in rows if r['lean_card'] == 8 and r['cr3_hyp']][SHARD::NSH]
out = []
for r in rows:
    d = r['d']
    E = pari.ellinit([-d * d, 0])
    pari('E = ellinit([-%d^2, 0])' % d)
    tries = [('ellrank(E)', 'ellrank(effort=0)', TLIM)]
    tries += [('ellrank(E, %d)' % e, 'ellrank(effort=%d)' % e, TLIM * k)
              for e, k in ((4, 1), (8, 2), (12, 3))]
    if d < 10 ** 5:
        tries.append(('[0, 0, 0, [ellheegner(E)]]', 'ellheegner', TLIM * 6))
    gens, how = [], 'none within limits'
    for cmd, label, tl in tries:
        try:
            res = pari('alarm(%d, %s)' % (tl, cmd))
        except BaseException:   # cysignals AlarmInterrupt is not an Exception
            res = [0, 0, 0, []]
        if len(res[3]) > 0:
            gens, how = list(res[3]), label
            break
    for a in r['cr3_hyp']:
        found = None
        for G in gens:
            for T in ([0], [0, 0], [d, 0], [-d, 0]):
                P = pari.elladd(E, G, T)
                if len(P) == 1:
                    continue
                x, y = to_fr(P[0]), to_fr(P[1])
                if x != 0 and y * y == x ** 3 - d * d * x and is_sq_rat(x / a):
                    found = (x, y)
                    break
            if found:
                break
        out.append(dict(d=d, a=a, how=how, found=found is not None,
                        x=str(found[0]) if found else None, y=str(found[1]) if found else None))
        print(d, a, how, 'FOUND' if found else 'NOT FOUND',
              ('x = %s (%d digits in num+den)' % (found[0] if len(str(found[0])) < 60 else '...',
               len(str(found[0].numerator)) + len(str(found[0].denominator)))) if found else '',
              flush=True)
json.dump(out, open('points40_%d.json' % SHARD, 'w'), indent=0)
print("found", sum(o['found'] for o in out), "of", len(out))
