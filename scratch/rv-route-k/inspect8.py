"""Smooth input #8 with m = 1: for random n' with the class beta on C_{n theta}, list dim Sel_2 of both
curves and the first coordinates (as sets of primes) of a basis of Sel_2(C_{n theta})."""
import sys, random
from fractions import Fraction as Fr
from collections import Counter
from descent_search import sqfQ, sqf_int, factor, oddprimes, necessary
from sel2cong import selmer, vec_of, first_coord_contains, F2Span
from beam_search import POOL
B = Fr(open('smooth8_B.txt').read().strip())
beta, theta = sqfQ(B), sqfQ(1 - B)
tp = sorted(factor(theta)); bp = sorted(factor(beta))
print("beta primes", bp, "\ntheta primes", tp, [p % 8 for p in tp])
rng = random.Random(11)
bad = set(bp) | set(tp)
pool = [q for q in POOL if q not in bad]
dims = Counter(); shown = 0; tried = 0
while shown < 12 and tried < 200000:
    tried += 1
    k = rng.randint(2, 10)
    combo = rng.sample(pool, k); prod = 1
    for q in combo: prod *= q
    if not necessary(prod, combo, beta): continue
    nt = sqf_int(beta * prod * theta)
    b2, g2 = selmer(nt, oddprimes(nt))
    if not first_coord_contains(b2, vec_of(beta, g2)): continue
    n = beta * prod
    b1, g1 = selmer(n, oddprimes(n))
    dims[(len(b1), len(b2))] += 1
    # first coordinates of Sel(C_nt) restricted to theta primes
    idx = {g: i for i, g in enumerate(g2)}
    tmask = 0
    for p in tp: tmask |= 1 << idx[p]
    sp = F2Span()
    for a, b in b2: sp.add(a & tmask)
    tsupp = [[tp[j] for j, p in enumerate(tp) if (r >> idx[p]) & 1] for r in sp.rows.values()]
    print(f"n' k={k}: dims (C_n, C_ntheta) = ({len(b1)}, {len(b2)}); theta-parts of first coords: {tsupp}", flush=True)
    shown += 1
print("tried", tried, "dims", dict(dims))
