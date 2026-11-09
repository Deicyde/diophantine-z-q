"""Full comparison of Sel_2 as a subspace: definition-based (sel2.py) vs Proposition 0 (prop0.py)."""
import random, sys
from sympy import primerange
from sel2 import selmer_primes, span
from prop0 import config_of, solve_system
random.seed(int(sys.argv[1])); N = int(sys.argv[2])
PR = list(primerange(3, 3000))
bad = 0; cnt = {1: 0, 3: 0, 5: 0, 7: 0}
for t in range(N):
    k = random.randint(1, 8)
    ps = sorted(random.sample(PR, k)); d = 1
    for p in ps: d *= p
    dim1, ker1, gens = selmer_primes(d, ps)
    S, c, L = config_of(ps); dim2, ker2 = solve_system(S, c, L)
    n = len(gens)
    def conv(v):  # prop0 layout -> sel2 layout (a: sign,2,primes ; b: sign,2,primes)
        a0, a1, b0, b1 = v & 1, v >> 1 & 1, v >> 2 & 1, v >> 3 & 1
        w = a0 | a1 << 1 | b0 << n | b1 << (n + 1)
        for i in range(k):
            w |= (v >> (4 + i) & 1) << (2 + i)
            w |= (v >> (4 + k + i) & 1) << (n + 2 + i)
        return w
    s1 = span(ker1); s2 = span([conv(v) for v in ker2])
    cnt[d % 8] += 1
    if s1 != s2:
        bad += 1; print("MISMATCH", ps, dim1, dim2)
print("N", N, cnt, "mismatches", bad)
