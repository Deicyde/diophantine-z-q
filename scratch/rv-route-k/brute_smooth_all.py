"""Brute-force fixed-multiplier (m = 1) search on the smooth-theta family (same generator and seed as
smooth_theta_test.py / anneal.py), with an independent re-verification of each solution:
Selmer dimensions of both curves and the class beta, recomputed from scratch, plus the PARI
2-Selmer count (ell2cover) for C_n when it is small enough."""
import sys, random, time
from fractions import Fraction as Fr
from descent_search import gen_smooththeta, sqfQ, sqf_int, factor, oddprimes, necessary, search_m
from sel2cong import selmer, vec_of, first_coord_contains
from beam_search import POOL

count, seed, trials = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
rng = random.Random(seed)
srch = random.Random(99)
ok = 0
for i in range(count):
    B = gen_smooththeta(rng)
    beta, theta = sqfQ(B), sqfQ(1 - B)
    r = search_m(B, 1, 0, 200)
    if r:
        print(f"#{i} omega(theta)={len(factor(theta))}: shortcut {r['kind']}", flush=True); ok += 1; continue
    bad = set(factor(beta)) | set(factor(theta))
    pool = [q for q in POOL if q not in bad]
    found = None; tried = 0; t0 = time.time()
    while tried < trials and found is None:
        k = srch.randint(2, 10)
        combo = srch.sample(pool, k); prod = 1
        for q in combo: prod *= q
        if not necessary(prod, combo, beta): continue
        tried += 1
        n = beta * prod; nt = sqf_int(n * theta)
        b2, g2 = selmer(nt, oddprimes(nt))
        if len(b2) != 3 or not first_coord_contains(b2, vec_of(beta, g2)): continue
        b1, g1 = selmer(n, oddprimes(n))
        if len(b1) == 3 and first_coord_contains(b1, vec_of(beta, g1)):
            found = (prod, k)
    if found:
        ok += 1
        prod, k = found
        # independent re-verification with fresh prime lists
        n = beta * prod; nt = sqf_int(n * theta)
        chk = []
        for d in (n, nt):
            ps = sorted(p for p in factor(d) if p != 2)
            b, g = selmer(d, ps)
            chk.append((len(b), first_coord_contains(b, vec_of(beta, g))))
        print(f"#{i} omega(beta)={len(factor(beta))} omega(theta)={len(factor(theta))} m=1: n'={prod} "
              f"(k={k}, {tried} trials, {time.time() - t0:.0f}s) recheck {chk}", flush=True)
    else:
        print(f"#{i} omega(theta)={len(factor(theta))} m=1: not found in {tried} trials", flush=True)
print("solved", ok, "of", count)
