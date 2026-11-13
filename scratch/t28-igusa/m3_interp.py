"""t28-igusa: identities M3. The Gram entries G_ij = pair(y_i, y_j) and a_ijk = p6(f, y_i y_j y_k)
(Lean normalizations: pair = polar of -disc, p6 = 60 * sum (-1)^i u_i v_{6-i} / C(6,i), coefficient
vectors c_i of x^i) of the Clebsch quadratic covariants y_1,y_2,y_3 as polynomials in the leaf's
J2, J4, J6, J10. Also the sizes of y_i as polynomials in a0..a6.
Run from the repo root: ~/pyenv/bin/python -I scratch/t28-igusa/m3_interp.py"""
import random, itertools, sympy as sp
x, z = sp.symbols('x z')
random.seed(20261113)
A = sp.symbols('a0:7')
def tv(phi, psi, k):
    m = sp.Poly(phi, x, z).total_degree(); n = sp.Poly(psi, x, z).total_degree()
    s = sum((-1)**j * sp.binomial(k, j) * sp.diff(phi, x, k - j, z, j) * sp.diff(psi, x, j, z, k - j) for j in range(k + 1))
    return sp.expand(sp.factorial(m - k) * sp.factorial(n - k) / (sp.factorial(m) * sp.factorial(n)) * s)
def ys(c):
    f = sp.expand(sum(ci * x**i * z**(6 - i) for i, ci in enumerate(c)))
    i4 = tv(f, f, 4); y1 = tv(f, i4, 4); y2 = tv(i4, y1, 2); y3 = tv(i4, y2, 2)
    return [[sp.expand(y).coeff(x, k).coeff(z, 2 - k) for k in range(3)] for y in (y1, y2, y3)]
# sizes, symbolic
Y = ys(A)
for n, y in enumerate(Y):
    print(f"y{n+1}: terms per coefficient", [len(sp.Poly(t, *A).terms()) for t in y], "degree", sp.Poly(Y[n][0], *A).total_degree())
pair = lambda u, v: 2*u[0]*v[2] + 2*u[2]*v[0] - u[1]*v[1]
w6 = [60, -10, 4, -3, 4, -10, 60]
p6 = lambda u, v: sum(w6[i]*u[i]*v[6-i] for i in range(7))
def cub(u, v, t):
    return [sum(u[i]*v[j]*t[k] for i in range(3) for j in range(3) for k in range(3) if i+j+k == m) for m in range(7)]
polys = {}
for line in open('scratch/pkg-I1/igusa_polys.txt'):
    k, v = line.split(' = '); polys[k] = sp.lambdify(A, sp.sympify(v, locals={f'a{i}': A[i] for i in range(7)}))
def Js(c): return [sp.Integer(polys[k](*c)) for k in ('J2', 'J4', 'J6', 'J10')]
deg = [3, 5, 7]
def jmons(d):  # monomials J2^p J4^q J6^r J10^s of degree d (J_{2k} has degree 2k)
    return [(p, q, r, s) for p in range(d//2+1) for q in range(d//4+1) for r in range(d//6+1) for s in range(d//10+1) if 2*p+4*q+6*r+10*s == d]
samples = []
while len(samples) < 60:
    c = [random.randint(-5, 5) for _ in range(7)]
    if Js(c)[3] == 0: continue
    samples.append((c, ys(c), Js(c)))
J2, J4, J6, J10 = sp.symbols('J2 J4 J6 J10')
def interp(val, d):
    ms = jmons(d)
    rows = [[sp.prod([v**e for v, e in zip(s[2], m)]) for m in ms] for s in samples[:45]]
    rhs = [val(s) for s in samples[:45]]
    M = sp.Matrix(rows); sol = (M.T*M).LUsolve(M.T*sp.Matrix(rhs))
    assert M*sol == sp.Matrix(rhs), "not in the span"
    P = sum(cf*J2**m[0]*J4**m[1]*J6**m[2]*J10**m[3] for cf, m in zip(sol, ms))
    for s in samples[45:]:
        assert P.subs({J2: s[2][0], J4: s[2][1], J6: s[2][2], J10: s[2][3]}) == val(s)
    return sp.expand(P)
out = []
for i in range(3):
    for j in range(i, 3):
        P = interp(lambda s: pair(s[1][i], s[1][j]), deg[i]+deg[j])
        out.append(f"G{i+1}{j+1} = {P}"); print(out[-1])
for t in itertools.combinations_with_replacement(range(3), 3):
    d = 1 + sum(deg[k] for k in t)
    P = interp(lambda s: p6(s[0], cub(s[1][t[0]], s[1][t[1]], s[1][t[2]])), d)
    out.append(f"a{t[0]+1}{t[1]+1}{t[2]+1} = {P}"); print(out[-1][:150], "...")
open('scratch/t28-igusa/m3_polys.txt', 'w').write("\n".join(out) + "\n")
print("M3: all 6 Gram entries and 10 cubic coefficients are polynomials in J2,J4,J6,J10 (interpolated on 45 sextics, checked on 15 fresh ones)")
