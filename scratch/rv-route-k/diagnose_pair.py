"""Diagnose a failing (B, m): local data of beta, theta and the outcome distribution over random
auxiliary products n' (k = 1..6) passing the necessary odd-prime conditions."""
import sys
import random
from collections import Counter
from fractions import Fraction as Fr
from descent_search import sqfQ, sqf_int, factor, oddprimes, BIGPOOL, necessary
from sel2cong import selmer, vec_of, first_coord_contains, rep2, image_Q2, cls2

B = Fr(sys.argv[1])
m = int(sys.argv[2])
rng = random.Random(1)
beta = sqfQ(m * B)
theta = sqfQ(m * (m - B))
bp = sorted(factor(beta))
tp = sorted(factor(theta))
print("beta =", beta, "primes", bp, " theta primes", tp)
print("beta 2-adic class", rep2(beta), "odd beta primes mod 8:", [p % 8 for p in bp if p != 2])
print("theta mod 16:", theta % 16)
pool = [q for q in BIGPOOL if beta % q != 0 and theta % q != 0][:300]
c = Counter()
classes = Counter()
for k in range(1, 7):
    for _ in range(400):
        combo = rng.sample(pool, k)
        prod = 1
        for q in combo:
            prod *= q
        if not necessary(prod, combo, beta):
            continue
        n = beta * prod
        out = []
        for d in (n, sqf_int(n * theta)):
            basis, gens = selmer(d, oddprimes(d))
            out.append((len(basis), first_coord_contains(basis, vec_of(beta, gens))))
        c[tuple(out)] += 1
        classes[(rep2(n), out[0][1] or out[1][1])] += 1
print("outcomes:", c.most_common(12))
print("(2-adic class of n, class beta present on some curve):", sorted(classes.items()))
