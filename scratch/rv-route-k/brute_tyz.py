"""Random auxiliary-prime search with the TYZ certificate (descent_tyz.good_tyz semantics), over the
multipliers in the usual order.  Usage: python brute_tyz.py B [trials_per_m] [nm]"""
import os, sys, random
KRIZ = os.environ.get("KRIZ") == "1"
from fractions import Fraction as Fr
import descent_search as ds
from sel2cong import selmer, vec_of, first_coord_contains
from tyz_smith import tyz
from beam_search import POOL


def good_tyz(d, beta):
    if ds.sqf_int(beta * d) == 1 or ds.sqf_int(-beta * d) == 1:
        return True
    b, g = selmer(d, ds.oddprimes(d))
    return len(b) == 3 and first_coord_contains(b, vec_of(beta, g)) and (KRIZ or tyz(abs(d)))


B = Fr(sys.argv[1]); trials = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
nm = int(sys.argv[3]) if len(sys.argv) > 3 else 12
rng = random.Random(5)
order = sorted(ds.DIVS, key=lambda m: (m < 0, abs(m)))[:nm]
for m in order:
    beta, theta = ds.sqfQ(m * B), ds.sqfQ(m * (m - B))
    if theta == 1:
        print("m", m, "theta = 1"); break
    bad = set(ds.factor(beta)) | set(ds.factor(theta))
    pool = [q for q in POOL if q not in bad]
    hit = None
    for t in range(trials):
        k = rng.randint(1, 6)
        combo = rng.sample(pool, k); prod = 1
        for q in combo: prod *= q
        if not ds.necessary(prod, combo, beta): continue
        n = beta * prod
        if good_tyz(ds.sqf_int(n * theta), beta) and good_tyz(n, beta):
            hit = prod; break
    print("m", m, "->", "n' = %d" % hit if hit else "none", flush=True)
    if hit: break
