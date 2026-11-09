"""Prop 0 (own system.py) against the own exact descent sel2.py: dimension and first coordinates."""
import random
from sel2 import selmer, has_first_coord
from system import solve, config_of, first_coord_in
rng = random.Random(99)
smallp = [p for p in range(3, 3000) if all(p % q for q in range(2, int(p ** .5) + 1))]
mism = 0
stats = {}
for t in range(30):
    k = rng.randint(1, 7)
    ps = sorted(rng.sample(smallp, k))
    d = 1
    for p in ps:
        d *= p
    dim, ker, gens = selmer(d, ps)
    c, L = config_of(ps)
    sols = solve(c, L)
    ok = (len(sols) == dim)
    # first coordinates: all 2^(k+1) odd signed divisors
    for s in range(2):
        for mask in range(1 << k):
            uset = [i for i in range(k) if mask >> i & 1]
            a = (-1) ** s
            for i in uset:
                a *= ps[i]
            if has_first_coord(ker, gens, a) != first_coord_in(sols, k, s, uset):
                ok = False
    stats[d % 8] = stats.get(d % 8, 0) + 1
    if not ok:
        mism += 1
        print("MISMATCH", ps, dim, len(sols))
print("30 curves, mismatches:", mism, "by d mod 8:", stats)
