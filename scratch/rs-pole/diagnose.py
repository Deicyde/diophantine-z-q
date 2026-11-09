"""Diagnose a failing input: for each m, find which place obstructs a Selmer class with first
coordinate beta on C_n / C_{n theta}, n = beta * n'."""
import sys, random, itertools
from fractions import Fraction as F
from selmer_descent import *

B = F(sys.argv[1])
a, b = FAMILIES[sys.argv[2]]
rng = random.Random(5)
primes = [int(p) for p in pari.primes(40)][2:]


def obstruction(N, beta):
    """Places p where no local-image element has first coordinate beta."""
    S = sorted(set(factor_primes(2 * a * b * (a - b) * N)) | {2})
    bad = []
    for p in S + [0]:
        want = 2 if p == 0 else (8 if p == 2 else 4)
        img = local_image(N, a, b, p, rng, want)
        if not any(u[0] == sqclass(beta, p) for u in img):
            bad.append(p)
    return bad


for m in [d for d in range(1, 2731) if 2730 % d == 0]:
    beta = core(m * B)
    theta = core(m * (m - B))
    if beta <= 1:
        continue
    stats = {}
    for k in range(0, 3):
        for combo in itertools.combinations(primes[:10], k):
            if any(beta % q == 0 or theta % q == 0 for q in combo):
                continue
            npr = 1
            for q in combo:
                npr *= q
            n = beta * npr
            o1, o2 = obstruction(n, beta), obstruction(n * theta, beta)
            key = (tuple(o1), tuple(o2))
            stats[key] = stats.get(key, 0) + 1
    print("m", m, "beta", beta, factor_primes(beta), "theta mod 8", theta % 8, "theta primes", factor_primes(theta))
    print("   obstruction places (C_n, C_ntheta) -> count:", stats)
