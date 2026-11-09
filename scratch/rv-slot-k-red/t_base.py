"""Base configurations of slot-k 2.3: {p*, q} (one auxiliary symbol), all classes and symbols.
Reports dim and whether +p* / -p* are first coordinates; and for |S|=3 whether some base exists
for each class of p*."""
import itertools
from prop0 import solve_system, contains_first
def lamc(c): return 1 if c % 4 == 3 else 0
res = {}
for cp, cq in itertools.product((1, 3, 5, 7), repeat=2):
    for x in (0, 1):
        S = ['p', 'q']; C = {'p': cp, 'q': cq}
        L = {('p', 'q'): x ^ (lamc(cp) & lamc(cq)), ('q', 'p'): x}   # [q/p] = x
        dim, ker = solve_system(S, C, L)
        plus = contains_first(ker, 1 << 4, 2); minus = contains_first(ker, 1 | 1 << 4, 2)
        if dim == 3 and (plus or minus):
            res.setdefault((cp, cq), []).append((x, plus, minus))
print("one auxiliary prime: dim 3 and +-p* in pi1:", res)
# two auxiliary primes
ok = {}
for cp, c1, c2 in itertools.product((1, 3, 5, 7), repeat=3):
    for bits in range(8):
        S = ['p', 'a', 'b']; C = {'p': cp, 'a': c1, 'b': c2}
        L = {}
        for k, (u, v) in enumerate([('p', 'a'), ('p', 'b'), ('a', 'b')]):
            bx = bits >> k & 1
            L[(u, v)] = bx; L[(v, u)] = bx ^ (lamc(C[u]) & lamc(C[v]))
        dim, ker = solve_system(S, C, L)
        for sgn in (0, 1):
            if dim == 3 and contains_first(ker, sgn | 1 << 4, 3):
                ok.setdefault(cp, set()).add((c1, c2, sgn))
print("two auxiliary primes, classes of p* with a base:", {k: len(v) for k, v in ok.items()})
