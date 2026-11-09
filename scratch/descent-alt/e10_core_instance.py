"""E10: admissible inputs whose beta contains an isotropic core of size K (primes = 1 mod 21840,
pairwise residues).  Proposition B predicts: no certificate with 1 <= omega(n') < K, and n' = 1 needs
omega(theta) >= K.  Random symbolic search over all multipliers (beta odd, = 5, 7 mod 8) for the
least r.  Usage: e10_core_instance.py K COUNT SEED RMAX SAMP"""
import sys, random, time
from common import *
import e6_family as E  # reuse solve() with the 'free' family
K, count, seed, RMAX, SAMP = map(int, sys.argv[1:6])
rng = random.Random(seed)
E.RMAX, E.SAMP, E.fam, E.rng = RMAX, SAMP, "free", rng
core = []
p = 1
while len(core) < K:
    p += 21840
    if pari.isprime(p) and all(pow(p, (c - 1) // 2, c) == 1 for c in core):
        core.append(p)
print("core", core, flush=True)
for i in range(count):
    B = gen_with_beta_primes(rng, core, dmult=2)
    t0 = time.time()
    hist = {}
    for m in DIVS:
        beta, theta = beta_theta(B, m)
        if beta % 2 == 0 or theta == 1 or abs(beta) % 8 not in (5, 7):
            continue
        r = E.solve(abs(beta), theta)
        hist[(r, len(oddprimes(theta)))] = hist.get((r, len(oddprimes(theta))), 0) + 1
    print(f"#{i} (least r, omega(theta)) over multipliers: {hist} ({time.time()-t0:.0f}s)", flush=True)
