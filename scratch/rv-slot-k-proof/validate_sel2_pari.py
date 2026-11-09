"""Compare sel2.py (own exact descent) with PARI ell2cover (length = dim Sel_2) on 30 random d."""
import random, sys
import cypari2
from sel2 import selmer
pari = cypari2.Pari()
rng = random.Random(4242)
smallp = [p for p in range(3, 400) if all(p % q for q in range(2, int(p ** .5) + 1))]
mism = 0
seen = {}
for t in range(30):
    k = rng.randint(1, 5)
    ps = sorted(rng.sample(smallp, k))
    d = 1
    for p in ps:
        d *= p
    dim, ker, gens = selmer(d, ps)
    E = pari.ellinit([0, 0, 0, -d * d, 0])
    dp = len(pari.ell2cover(E))
    seen[(d % 8, dim)] = seen.get((d % 8, dim), 0) + 1
    if dim != dp:
        mism += 1
        print("MISMATCH", d, dim, dp)
print("tested 30, mismatches", mism, "classes (d mod 8, dim):", sorted(seen.items()))
