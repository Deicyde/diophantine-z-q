"""Brute-force random search for a fixed (B, m): n' = product of k random primes (k = 2..10) from
the primes up to 10^6, filtered by the necessary odd-prime conditions; test the class beta on
C_{n theta} first (the rare event), then on C_n, then the two Selmer dimensions.
Usage: python brute_fixed_m.py B m trials seed"""
import sys, random, time
from fractions import Fraction as Fr
from descent_search import sqfQ, sqf_int, factor, oddprimes, necessary
from sel2cong import selmer, vec_of, first_coord_contains
from beam_search import POOL

B = Fr(sys.argv[1]); m = int(sys.argv[2]); trials = int(sys.argv[3]); rng = random.Random(int(sys.argv[4]))
beta = sqfQ(m * B); theta = sqfQ(m * (m - B))
bad = set(factor(beta)) | set(factor(theta))
pool = [q for q in POOL if q not in bad]
t0 = time.time(); stats = dict(tried=0, pres_nt=0, pres_both=0, min_nt=0)
for _ in range(trials):
    k = rng.randint(2, 10)
    combo = rng.sample(pool, k)
    prod = 1
    for q in combo: prod *= q
    if not necessary(prod, combo, beta):
        continue
    stats["tried"] += 1
    n = beta * prod; nt = sqf_int(n * theta)
    b2, g2 = selmer(nt, oddprimes(nt))
    if not first_coord_contains(b2, vec_of(beta, g2)):
        continue
    stats["pres_nt"] += 1
    b1, g1 = selmer(n, oddprimes(n))
    if not first_coord_contains(b1, vec_of(beta, g1)):
        continue
    stats["pres_both"] += 1
    if len(b2) == 3:
        stats["min_nt"] += 1
    if len(b1) == 3 and len(b2) == 3:
        print("FOUND n' =", prod, "k =", k, stats, f"{time.time() - t0:.0f}s", flush=True)
        break
print("final", stats, f"{time.time() - t0:.0f}s")
