"""Genus sums for squarefree odd n, from class groups (PARI) and from Rédei bits (as in Lean Defs.lean)."""
import cypari2
from functools import lru_cache
pari = cypari2.Pari()
pari.allocatemem(2 * 10**9)

def primes_of(n):
    f = pari.factor(n)
    ps = [int(p) for p in f[0]]
    assert all(int(e) == 1 for e in f[1]), "not squarefree"
    return ps

@lru_cache(None)
def gCl(d):
    """parity of #(Cl(Q(sqrt -d))^2), d>0 squarefree; field discriminant -d or -4d."""
    D = -d if d % 4 == 3 else -4 * d
    cyc = [int(c) for c in pari.quadclassunit(D)[1]]
    # #Cl^2 = prod c_i / gcd(c_i,2) ; odd iff every c_i has 2-adic valuation <= 1
    return int(all(c % 4 != 0 for c in cyc))

def legbit(p, q):  # additive Legendre symbol (q/p), p odd prime
    return 0 if pari.kronecker(q, p) == 1 else 1

def redei_g(ps, B):
    """Rédei formula as Lean redeiG: B = list of indices into ps."""
    y = [1 if ps[i] % 4 == 3 else 0 for i in range(len(ps))]
    z = [1 if ps[i] % 8 in (3, 5) else 0 for i in range(len(ps))]
    def a(i, j): return legbit(ps[i], ps[j])
    def lap(U):
        return {(i, j): (sum(a(i, k) for k in U if k != i) % 2 if i == j else a(i, j)) for i in U for j in U}
    def det2(M, idx):
        # det over F2 of M restricted to idx
        rows = [[M[(i, j)] for j in idx] for i in idx]
        n = len(rows); rk = 0
        for c in range(n):
            piv = next((r for r in range(rk, n) if rows[r][c]), None)
            if piv is None: return 0
            rows[rk], rows[piv] = rows[piv], rows[rk]
            for r in range(n):
                if r != rk and rows[r][c]:
                    rows[r] = [x ^ yv for x, yv in zip(rows[r], rows[rk])]
            rk += 1
        return 1
    L = lap(B)
    kap = {rho: det2(L, [i for i in B if i != rho]) for rho in B}
    if sum(y[i] for i in B) % 2 == 1:
        return sum(y[r] * kap[r] for r in B) % 2
    return sum(z[r] * kap[r] for r in B) % 2

def set_partitions(items):
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for p in set_partitions(rest):
        yield [[first]] + p
        for k in range(len(p)):
            yield p[:k] + [[first] + p[k]] + p[k + 1:]

def prod(xs):
    v = 1
    for x in xs: v *= x
    return v

def genus_sums(n, use_redei=False):
    """returns (T5a, T5b, Lambda1(n)) parities as set-partition sums, g from class groups (or Rédei)."""
    ps = primes_of(n)
    idx = list(range(len(ps)))
    T5a = T5b = 0
    for pi in set_partitions(idx):
        ds = [prod(ps[i] for i in B) for B in pi]
        cs = [d % 8 for d in ds]
        a_ok = cs.count(5) == 1 and all(c in (1, 5) for c in cs)
        b_ok = cs.count(7) == 1 and cs.count(3) == 1 and all(c in (1, 3, 7) for c in cs)
        if not (a_ok or b_ok): continue
        if use_redei:
            w = prod(redei_g(ps, B) for B in pi)
        else:
            w = prod(gCl(d) for d in ds)
        if a_ok: T5a ^= w
        if b_ok: T5b ^= w
    return T5a, T5b

def analytic_rank(n):
    E = pari.ellinit([0, 0, 0, -n * n, 0])
    return int(pari.ellanalyticrank(E)[0])
