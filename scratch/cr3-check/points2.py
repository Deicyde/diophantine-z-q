"""Second pass of step 4 for the pairs (d, a) that points.py did not settle: ellheegner (d < 2*10^6)
and ellrank with effort 20 and 30, each under a PARI alarm. Also the BSD-predicted canonical height
of a generator (assuming #Sha = 1, as Sha[2] = 0 here): L'(1) / ellbsd(E), for d < 2*10^6.
Usage: python points2.py d TLIM -> points2_d.json"""
import json, sys
from fractions import Fraction as Fr
from math import isqrt
import cypari2
pari = cypari2.Pari(); pari.allocatemem(2 * 10**9)


def is_sq_rat(r):
    r = Fr(r)
    return r >= 0 and isqrt(r.numerator) ** 2 == r.numerator and isqrt(r.denominator) ** 2 == r.denominator


def to_fr(z):
    return Fr(int(pari.numerator(z)), int(pari.denominator(z)))


d, TLIM = int(sys.argv[1]), int(sys.argv[2])
row = [r for r in json.load(open('cmp40.json')) if r['d'] == d][0]
E = pari.ellinit([-d * d, 0])
pari('E = ellinit([-%d^2, 0])' % d)
pred = None
if d < 2 * 10 ** 6:
    ar = pari.ellanalyticrank(E)
    pred = float(ar[1] / pari.ellbsd(E))
    print(d, 'BSD-predicted height of a generator (Sha = 1):', pred, flush=True)
tries = []
if d < 2 * 10 ** 6:
    tries.append(('[0, 0, 0, [ellheegner(E)]]', 'ellheegner', 2 * TLIM))
tries += [('ellrank(E, 20)', 'ellrank(effort=20)', TLIM), ('ellrank(E, 30)', 'ellrank(effort=30)', TLIM)]
gens, how = [], 'none within limits'
for cmd, label, tl in tries:
    try:
        res = pari('alarm(%d, %s)' % (tl, cmd))
    except BaseException:
        res = [0, 0, 0, []]
    print(d, label, 'points:', len(res[3]), flush=True)
    if len(res[3]) > 0:
        gens, how = list(res[3]), label
        break
out = []
for a in row['cr3_hyp']:
    found = None
    for G in gens:
        for T in ([0], [0, 0], [d, 0], [-d, 0]):
            P = pari.elladd(E, G, T)
            if len(P) == 1:
                continue
            x, y = to_fr(P[0]), to_fr(P[1])
            if x != 0 and y * y == x ** 3 - d * d * x and is_sq_rat(x / a):
                found = (x, y); break
        if found: break
    hgt = float(pari.ellheight(E, gens[0])) if gens else None
    out.append(dict(d=d, a=a, how=how, found=found is not None, pred_height=pred, height=hgt,
                    x=str(found[0]) if found else None, y=str(found[1]) if found else None))
    print(d, a, how, 'FOUND' if found else 'NOT FOUND',
          ('(%d digits in num+den of x, height %.1f)' % (len(str(found[0].numerator)) + len(str(found[0].denominator)), hgt)) if found else '', flush=True)
json.dump(out, open('points2_%d.json' % d, 'w'), indent=0)
