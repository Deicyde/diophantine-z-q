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
        if (c[6] != 0 or c[5] != 0) and pari("poldisc(" + sp.sstr(f).replace("**", "^") + ")") != 0: return c
polys = {}
idx = {2: 0, 4: 1, 6: 2, 10: 4}
gen6 = sum(a[i]*x**i for i in range(7))
polys[10] = sp.expand(256*sp.discriminant(gen6, x))   # J10 = 2^8 disc (binary-form disc; PARI normalizes via 4f)
print(f"J10 := 2^8 * disc(generic sextic): {len(sp.Poly(polys[10], *a).terms())} terms")
for k in (1, 2, 3):
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
# degree-5 check: y^2 = x^5 - 1 gives J10 = 800000 = 2^8 * 5^5 in PARI
assert polys[10].subs({a[0]: -1, a[1]: 0, a[2]: 0, a[3]: 0, a[4]: 0, a[5]: 1, a[6]: 0}) == 800000
assert igusa([-1, 0, 0, 0, 0, 1, 0])[4] == 800000
print("degree-5 example x^5 - 1: J10 = 800000 (PARI agrees)")
# Lean code
def lean_expr(P):
    terms = []
    for mon, cf in sp.Poly(P, *a).terms():
        m = " * ".join(f"a {i}" + (f" ^ {e}" if e > 1 else "") for i, e in enumerate(mon) if e > 0)
        cf = sp.Rational(cf)
        assert cf.q == 1
        terms.append(f"({cf.p} : K) * {m}")
    return " +\n    ".join(terms)
with open('scratch/pkg-I1/igusa_lean.txt', 'w') as fh:
    for w in (2, 4, 6, 10):
        fh.write(f"def J{w} (a : Fin 7 → K) : K :=\n    {lean_expr(polys[w])}\n\n")
print("written igusa_lean.txt")
