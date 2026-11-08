"""E1: no auxiliary prime (n = beta).  For each admissible B and each of the 64 multipliers record
|beta theta| mod 8 (root number of C_{beta theta}), dim Sel2(C_{beta theta}), and whether beta is a
first coordinate.  Usage: e1_multiplier_stats.py FAMILY COUNT SEED"""
import sys, time, random
from collections import Counter
from common import *

fam, count, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
rng = random.Random(seed)
P3 = [p for p in map(int, pari.primes(200)) if p % 4 == 3 and p > 13]
P1 = [p for p in map(int, pari.primes(200)) if p % 4 == 1 and p > 13]
tot = Counter()
for i in range(count):
    if fam == "random":
        B = gen_random(rng)
    elif fam.startswith("p3x"):   # beta gets k primes = 3 mod 4
        k = int(fam[3:])
        B = gen_with_beta_primes(rng, rng.sample(P3, k))
    elif fam.startswith("p1x"):
        k = int(fam[3:])
        B = gen_with_beta_primes(rng, rng.sample(P1, k))
    t0 = time.time()
    succ = []
    c = Counter()
    for m in DIVS:
        beta, theta = beta_theta(B, m)
        d = sqf_int(beta * theta)
        r = abs(d) % 8
        rn = -1 if r in (5, 6, 7) else 1
        if theta == 1:
            succ.append(m); c["theta1"] += 1; continue
        dim, inpi = info(d, beta)
        c[(rn, dim, inpi)] += 1
        if dim == 3 and inpi:
            succ.append(m)
    tot.update(c)
    b1 = sqfQ(B)
    print(f"#{i} beta_1={b1} omega(beta)={len(factor(b1))} p3(beta)={sum(1 for p in factor(b1) if p%4==3 and p not in S0)} "
          f"succ m: {len(succ)} {succ[:8]} stats {dict(c)} ({time.time()-t0:.1f}s)", flush=True)
print("TOTAL", dict(tot))
