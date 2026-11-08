"""For a fixed (B, m): search n' (random products of up to 6 primes from a large pool, filtered by the
necessary odd-prime conditions) for which the class beta lies in Sel_2 of BOTH C_n and C_{n theta},
ignoring the dimension condition.  Reports the counts of (present on C_n, present on C_ntheta)."""
import sys, random
from fractions import Fraction as Fr
from collections import Counter
from descent_search import sqfQ, sqf_int, factor, oddprimes, necessary
from sel2cong import selmer, vec_of, first_coord_contains
from beam_search import POOL

B = Fr(sys.argv[1]); m = int(sys.argv[2]); trials = int(sys.argv[3]) if len(sys.argv) > 3 else 3000
rng = random.Random(7)
beta = sqfQ(m * B); theta = sqfQ(m * (m - B))
bad = set(factor(beta)) | set(factor(theta))
cnt = Counter(); done = 0
while done < trials:
    k = rng.randint(1, 6)
    combo = [q for q in rng.sample(POOL, k) if q not in bad]
    prod = 1
    for q in combo: prod *= q
    if not necessary(prod, combo, beta):
        continue
    done += 1
    out = []
    for d in (beta * prod, sqf_int(beta * prod * theta)):
        b, g = selmer(d, oddprimes(d))
        out.append(first_coord_contains(b, vec_of(beta, g)))
    cnt[tuple(out)] += 1
print("beta", beta, "theta", theta)
print("(present on C_n, present on C_ntheta):", dict(cnt))
