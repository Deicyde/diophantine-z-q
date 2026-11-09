"""Cross-check: Proposition 0 system (prop0.py, from the text) vs the definition-based descent
(sel2.py) on random odd squarefree d, all classes mod 8. Compares dimension and, for every
signed divisor a of 2d... (all first coordinates), membership in pi_1."""
import random, sys
from sympy import primerange
from sel2 import selmer_primes, first_coords, reduce, vec_of
from prop0 import config_of, solve_system, first_coord_mask, contains_first
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
PR = list(primerange(3, 3000))
bad = 0; cnt = {1: 0, 3: 0, 5: 0, 7: 0}
N = int(sys.argv[2]) if len(sys.argv) > 2 else 300
for t in range(N):
    k = random.randint(1, 7)
    ps = sorted(random.sample(PR, k))
    d = 1
    for p in ps: d *= p
    dim1, ker1, gens = selmer_primes(d, ps)
    S, c, L = config_of(ps)
    dim2, ker2 = solve_system(S, c, L)
    cnt[d % 8] += 1
    # compare first-coordinate spaces: map sel2 a-vector (bits: 0 sign,1 two, 2.. primes) to prop0 layout
    fc1 = first_coords(ker1, gens)
    ok = dim1 == dim2
    for trial in range(8):
        a0 = random.randint(0, 1); a1 = random.randint(0, 1)
        u = [random.randint(0, 1) for _ in ps]
        v1 = a0 | (a1 << 1)
        v2 = a0 | (a1 << 1)
        for i, b in enumerate(u):
            v1 |= b << (2 + i); v2 |= b << (4 + i)
        m1 = reduce(v1, fc1) == 0
        m2 = contains_first(ker2, v2, len(ps))
        ok = ok and (m1 == m2)
    if not ok:
        bad += 1; print("MISMATCH", d, ps, dim1, dim2)
print("trials", N, "by class", cnt, "mismatches", bad)
