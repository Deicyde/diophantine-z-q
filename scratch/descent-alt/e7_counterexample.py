"""E7: admissible B for which no multiplier works without auxiliary primes, unconditionally:
for all 64 signed divisors m of 2730, theta_m != 1 and beta_m is NOT a first coordinate of
Sel_2(C_{beta_m theta_m}) (so C_{beta theta} has no rational point with abscissa in beta Q*^2, and
n = beta, n = beta theta both fail).  Usage: e7_counterexample.py K SEED TRIES"""
import sys, random
from common import *
K, seed, tries = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
rng = random.Random(seed)
P3 = [p for p in map(int, pari.primes(300)) if p % 4 == 3 and p > 13]
found = 0
for t in range(tries):
    B = gen_with_beta_primes(rng, rng.sample(P3, K))
    weak = True; strong = True
    for m in DIVS:
        beta, theta = beta_theta(B, m)
        if theta == 1:
            weak = strong = False; break
        d = sqf_int(beta * theta)
        dim, inpi = info(d, beta)
        if inpi:
            strong = False
            if dim == 3:
                weak = False; break
    if strong:
        found += 1
        print(f"UNCONDITIONAL B = {B}", flush=True)
    elif weak:
        print(f"certificate-only failure B = {B}", flush=True)
print("tries", tries, "unconditional", found)
