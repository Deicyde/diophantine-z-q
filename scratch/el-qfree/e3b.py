"""E3b: more instances/multipliers for E3 (same test), primes p = 3 mod 4 of good reduction
(f squarefree mod p and degree preserved)."""
import e3_cmfactor as E
from e3_cmfactor import pari
for (n, h, s0, eta, m) in [(1, 2, 2, 1, -1), (1, 2, 2, -1, 3), (2, 2, 4, 1, 1)]:
    f = E.curve_poly(n, 1, h, s0, eta, m)
    d = pari.poldegree(f); done = 0
    print((n, h, s0, eta, m), 'deg', d, flush=True)
    for p in (19, 23, 43, 47, 59, 67, 71, 79, 83):
        if done: break
        if pari.pollead(f) % p == 0: continue
        r = E.test(f, p)
        if isinstance(r, dict): print('  ', r, flush=True); done = 1
