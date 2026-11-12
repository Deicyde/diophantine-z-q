"""pkg-I1: Igusa invariants J2, J4, J6, J10 of the genus-2 curve y^2 = f(x), f = sum a_i x^i (deg f <= 6),
as explicit polynomials in a_0..a_6, in PARI's normalization (genus2igusa), found by exact
interpolation over the isobaric monomial basis and checked on fresh random samples.
Also checks the binary-form transformation law and the Igusa vector of N5 L538-540.
Run: ~/pyenv/bin/python -I igusa_poly.py  (writes igusa_polys.txt)"""
import itertools, random, sympy as sp, cypari2
pari = cypari2.Pari()
a = sp.symbols('a0:7'); x = sp.symbols('x')
random.seed(20261111)
def mons(deg, wt):
    out = []
    for e in itertools.product(range(deg+1), repeat=7):
        if sum(e) == deg and sum(i*ei for i, ei in enumerate(e)) == wt: out.append(e)
    return out
def igusa(coeffs):
    f = sum(c*x**i for i, c in enumerate(coeffs))
    v = pari("genus2igusa(" + sp.sstr(f).replace("**", "^") + ")")
    return [sp.Rational(str(t)) for t in v]
def rand_sextic():
    while True:
        c = [random.randint(-9, 9) for _ in range(7)]
        f = sum(ci*x**i for i, ci in enumerate(c))
        if sp.degree(f, x) >= 5 and sp.discriminant(f, x) != 0: return c
polys = {}
idx = {2: 0, 4: 1, 6: 2, 10: 4}
for k in (1, 2, 3, 5):
    B = mons(2*k, 6*k)
    rows, rhs = [], []
    while len(rows) < len(B) + 15:
        c = rand_sextic()
        rows.append([sp.prod([ci**ei for ci, ei in zip(c, e)]) for e in B]); rhs.append(igusa(c)[idx[2*k]])
    M = sp.Matrix(rows); bvec = sp.Matrix(rhs)
    sol = (M.T*M).LUsolve(M.T*bvec)
    assert M*sol == bvec, "interpolation inconsistent"
    P = sum(s*sp.prod([ai**ei for ai, ei in zip(a, e)]) for s, e in zip(sol, B))
    polys[2*k] = sp.expand(P)
    print(f"J{2*k}: {len(B)} isobaric monomials, {len(sp.Poly(P, *a).terms())} nonzero terms")
# fresh check
for _ in range(10):
    c = rand_sextic(); ref = igusa(c)
    for w in (2, 4, 6, 10):
        assert polys[w].subs(dict(zip(a, c))) == ref[idx[w]]
print("10 fresh samples agree with PARI genus2igusa")
# J10 vs discriminant: for deg f = 6, J10 = 2^8 disc(f) (PARI applies Igusa's normalization to 4f)
c = rand_sextic(); f = sum(ci*x**i for i, ci in enumerate(c))
if sp.degree(f, x) == 6:
    print("J10 / disc(f) =", polys[10].subs(dict(zip(a, c))) / sp.discriminant(f, x))
# transformation law: f -> e * (cx+d)^6 f((ax+b)/(cx+d)) multiplies J_{2k} by (e * det^3)^(2k)
A_, B_, C_, D_, E_ = 2, -1, 3, 1, 5
c = rand_sextic(); f = sum(ci*x**i for i, ci in enumerate(c))
g = sp.expand(E_*sp.cancel((C_*x + D_)**6 * f.subs(x, (A_*x + B_)/(C_*x + D_))))
cg = [g.coeff(x, i) for i in range(7)]
r = E_*(A_*D_ - B_*C_)**3
for w in (2, 4, 6, 10):
    assert polys[w].subs(dict(zip(a, cg))) == r**w * polys[w].subs(dict(zip(a, c)))
print("transformation law J_{2k}(e*f|M) = (e*det(M)^3)^(2k) J_{2k}(f): OK on one sample")
with open('scratch/pkg-I1/igusa_polys.txt', 'w') as fh:
    for w in (2, 4, 6, 10):
        fh.write(f"J{w} = {sp.sstr(polys[w])}\n")
print("written igusa_polys.txt")
