"""Adversarial family with theta (for m = 1) a product of 4..9 small primes, built as
N = D^2 - theta0 Y^2.  For m = 1 only: try the shortcuts (n' = 1, n' = theta) and then the two-phase
auxiliary-prime search."""
import sys, random
from fractions import Fraction as Fr
from descent_search import gen_smooththeta, search_m, sqfQ, factor
from twophase import solve

count, seed = int(sys.argv[1]), int(sys.argv[2])
rng = random.Random(seed)
ok = 0
for i in range(count):
    B = gen_smooththeta(rng)
    beta, theta = sqfQ(B), sqfQ(1 - B)
    r = search_m(B, 1, 0, 200)
    if r:
        how, npr = "shortcut", r.get("nprime", 1)
    else:
        how, npr = solve(B, 1)
    ok += how is not None
    print(f"#{i} omega(beta)={len(factor(beta))} theta={theta} omega(theta)={len(factor(theta))} "
          f"m=1: {how} n'={npr}", flush=True)
print("solved", ok, "of", count)
