import sys, random
sys.argv = ["x"]; import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "descent-alt"))
from common import *
for seed in list(range(0, 50)) + [2024, 2025, 2026, 12345]:
    for MAXK in (8, 9, 10, 11, 12, 14):
        rng = random.Random(seed)
        P3 = [p for p in map(int, pari.primes(300)) if p % 4 == 3 and p > 13]
        while True:
            B = gen_random(rng)
            ms = [m for m in DIVS if beta_theta(B, m)[0] % 2 and beta_theta(B, m)[1] != 1
                  and abs(beta_theta(B, m)[0]) % 8 in (5, 7)
                  and len(oddprimes(beta_theta(B, m)[0])) + len(oddprimes(beta_theta(B, m)[1])) <= MAXK]
            if ms: break
        m = rng.choice(ms)
        beta, theta = beta_theta(B, m)
        if m == -35 and len(oddprimes(beta)) == 4 and len(oddprimes(theta)) == 3:
            print("FOUND", seed, MAXK, B); sys.exit()
print("none")
