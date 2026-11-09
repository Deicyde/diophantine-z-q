"""Compare symsel (Legendre data only) with the exact sel2cong 2-Selmer groups on random odd d."""
import random, sys
from common import *
import symsel
rng = random.Random(int(sys.argv[1]))
pr = [int(p) for p in pari.primes(400)][1:]
bad = 0; n = 0; byclass = {}
for t in range(int(sys.argv[2])):
    k = rng.randint(1, 7)
    ps = sorted(rng.sample(pr, k))
    d = 1
    for p in ps: d *= p
    basis, gens = selmer(d, ps)
    cfg = symsel.config_of(ps)
    ds = symsel.selmer_dim(cfg)
    ok = ds == len(basis)
    # first coordinate check for a random divisor
    um = rng.randrange(1 << k)
    a = 1
    for i in range(k):
        if um >> i & 1: a *= ps[i]
    ok2 = symsel.has_first(cfg, um) == first_coord_contains(basis, vec_of(a, gens))
    n += 1
    byclass[d % 8] = byclass.get(d % 8, 0) + 1
    if not (ok and ok2):
        bad += 1
        print("MISMATCH", ps, d % 8, ds, len(basis), ok2)
print("tested", n, "mismatches", bad, "by class", byclass)
