# Certificate (pure Python, Fractions): express D * n_i^2 (D 6-smooth) as a Z-combination of the
# coordinates (in N5's basis) of x e_k xbar, x = n0 + n1 i + n2 (1+j)/2 + n3 (i+ij)/2, B = (2,-3).
from fractions import Fraction as F
from itertools import combinations_with_replacement as cwr
from math import lcm
# polynomials: dict monomial(tuple of 4 exps) -> Fraction
def padd(*ps):
    r = {}
    for p in ps:
        for m, c in p.items(): r[m] = r.get(m, 0) + c
    return {m: c for m, c in r.items() if c != 0}
def pscale(c, p): return {m: c * v for m, v in p.items() if c * v != 0}
def pmul(p, q):
    r = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            m = tuple(a + b for a, b in zip(m1, m2)); r[m] = r.get(m, 0) + c1 * c2
    return {m: c for m, c in r.items() if c != 0}
def const(c): return {(0,0,0,0): F(c)} if c else {}
def var(i): return {tuple(1 if j == i else 0 for j in range(4)): F(1)}
def qmul(x, y):
    a1,b1,c1,d1 = x; a2,b2,c2,d2 = y
    return (padd(pmul(a1,a2), pscale(2,pmul(b1,b2)), pscale(-3,pmul(c1,c2)), pscale(6,pmul(d1,d2))),
            padd(pmul(a1,b2), pmul(b1,a2), pscale(3,pmul(c1,d2)), pscale(-3,pmul(d1,c2))),
            padd(pmul(a1,c2), pmul(c1,a2), pscale(2,pmul(b1,d2)), pscale(-2,pmul(d1,b2))),
            padd(pmul(a1,d2), pmul(d1,a2), pmul(b1,c2), pscale(-1,pmul(c1,b2))))
def star(x): return (x[0], pscale(-1,x[1]), pscale(-1,x[2]), pscale(-1,x[3]))
def comb(m):
    h = F(1,2)
    return (padd(m[0], pscale(h,m[2])), padd(m[1], pscale(h,m[3])), pscale(h,m[2]), pscale(h,m[3]))
def coord(x): return [padd(x[0], pscale(-1,x[2])), padd(x[1], pscale(-1,x[3])), pscale(2,x[2]), pscale(2,x[3])]
E = [comb([const(1),{},{},{}]), comb([{},const(1),{},{}]), comb([{},{},const(1),{}]), comb([{},{},{},const(1)])]
X = comb([var(i) for i in range(4)])
entries = []
for k in range(4):
    v = coord(qmul(qmul(X, E[k]), star(X)))
    for l in range(4):
        assert all(c.denominator == 1 for c in v[l].values())
        entries.append(((k, l), v[l]))
mons = [tuple(sum(1 for t in pair if t == j) for j in range(4)) for pair in cwr(range(4), 2)]
for kl, e in entries:
    print(kl, {m: int(c) for m, c in e.items()})
# solve M^T c = target over Q (16 unknowns, 10 equations) by Gaussian elimination, free vars = 0
A = [[entries[r][1].get(m, F(0)) for r in range(16)] for m in mons]  # 10 x 16
def solve(target):
    rows = [A[i][:] + [target[i]] for i in range(10)]
    piv = []; r = 0
    for c in range(16):
        pr = next((i for i in range(r, 10) if rows[i][c] != 0), None)
        if pr is None: continue
        rows[r], rows[pr] = rows[pr], rows[r]
        pv = rows[r][c]; rows[r] = [v / pv for v in rows[r]]
        for i in range(10):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]; rows[i] = [a - f * b for a, b in zip(rows[i], rows[r])]
        piv.append(c); r += 1
    assert all(rows[i][16] == 0 for i in range(r, 10)), "inconsistent"
    sol = [F(0)] * 16
    for i, c in enumerate(piv): sol[c] = rows[i][16]
    return sol, len(piv)
for i in range(4):
    target = [F(1) if m == tuple(2 if j == i else 0 for j in range(4)) else F(0) for m in mons]
    sol, rk = solve(target)
    D = lcm(*[s.denominator for s in sol])
    print("i", i, "rank", rk, "D", D, [int(s * D) for s in sol])
# all 10 monomials n_a n_b
for m in mons:
    target = [F(1) if mm == m else F(0) for mm in mons]
    sol, rk = solve(target)
    D = lcm(*[s.denominator for s in sol])
    print("mon", m, "D", D, [(r, int(s * D)) for r, s in enumerate(sol) if s != 0])
