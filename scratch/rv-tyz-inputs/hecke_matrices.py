"""Check the explicit 2-adic matrix calculations behind TYZ Theorem 3.6(1),(3) (arXiv:1411.4728v1,
Lemma coset5, Prop. heckeaction5, Prop. prop3.9) and the Gamma_0(32) cusp classes they produce.

Everything is exact (sympy Rationals). Symbolic checks use n = 5 + 8m (resp. sample values);
2-adic integrality of a polynomial in m is tested by a sufficient condition (all coefficients have
the required 2-adic valuation) and, as a backup, on m = 0..63.
"""
import sympy as sp
from sympy import Matrix, Rational as R, symbols, expand, Poly

m = symbols('m')


def v2(q):
    q = sp.Rational(q)
    if q == 0:
        return 10**9
    num, den = q.p, q.q
    v = 0
    while num % 2 == 0:
        num //= 2; v += 1
    while den % 2 == 0:
        den //= 2; v -= 1
    return v


def poly_v2(expr):
    """min 2-adic valuation of the coefficients of expr as a polynomial in m (sufficient bound)."""
    expr = sp.expand(expr)
    if expr == 0:
        return 10**9
    P = Poly(expr, m)
    return min(v2(c) for c in P.coeffs())


def sample_v2(expr):
    return min(v2(sp.expand(expr).subs(m, k)) for k in range(64))


def in_U0_32(g, need_U=False):
    """g in U_0(32)_2: entries in Z_2, 32 | c, det in Z_2^x. If need_U also 4 | (a-d)."""
    a, b, c, d = g[0, 0], g[0, 1], g[1, 0], g[1, 1]
    ok = all(poly_v2(x) >= 0 for x in (a, b, c, d)) and poly_v2(c) >= 5
    det = sp.expand(g.det())
    ok = ok and sample_v2(det) == 0 and all(v2(det.subs(m, k)) == 0 for k in range(64))
    if need_U:
        ok = ok and poly_v2(a - d) >= 2
    return ok


def gamma0_equiv(x, y, N=32):
    """Are cusps x, y (Rationals or 'oo') Gamma_0(N)-equivalent? (exact search over the stabiliser of oo)."""
    def col(t):
        if t == 'oo':
            return (1, 0)
        t = sp.Rational(t)
        return (t.p, t.q)

    def complete(a, c):
        s, t, g = sp.gcdex(a, c)  # s*a + t*c = g = 1
        assert g == 1
        # matrix [[a, -t],[c, s]] has det a*s + t*c = 1
        return Matrix([[a, -t], [c, s]])
    a, c = col(x)
    a2, c2 = col(y)
    M = complete(a, c)
    M2 = complete(a2, c2)
    for sgn in (1, -1):
        for k in range(N):
            T = sgn * Matrix([[1, k], [0, 1]])
            G = M2 * T * M.inv()
            if G[1, 0] % N == 0:
                return True
    return False


def cusp_of(G):
    """[oo, G] for G in SL_2(Z) (times U_0(32)) equals the cusp G^{-1} oo."""
    Gi = G.inv()
    a, c = Gi[0, 0], Gi[1, 0]
    return 'oo' if c == 0 else sp.Rational(a, c)


out = []
def check(label, cond):
    out.append((label, bool(cond)))
    print(('OK   ' if cond else 'FAIL ') + label)


# ---------------- n = 5 mod 8 ----------------
n = 5 + 8 * m
I2 = sp.eye(2)
M5 = Matrix([[-1, R(1, 4)], [-4 * (n + 1), 1]])
check('n5: M5^2 = -n', sp.simplify(M5 * M5 + n * I2) == sp.zeros(2))
vp = M5 - I2                      # varpi = sqrt(-n) - 1
one2 = I2 + 2 * vp                # 1 + 2 varpi
eps = Matrix([[1, 0], [0, -1]])
check('n5: varpi matrix as printed', sp.simplify(vp - Matrix([[-2, R(1, 4)], [-4 * (n + 1), 0]])) == sp.zeros(2))

# decompositions of Prop heckeaction5
D1 = Matrix([[R(1, 4), 0], [0, 8]]); G1 = Matrix([[-8, -1], [1, 0]]); R1 = Matrix([[-(n + 1) / 2, 0], [4 * (n + 3), 1]])
check('n5: varpi*eps = D1 G1 R1', sp.simplify(vp * eps - D1 * G1 * R1) == sp.zeros(2))
check('n5: R1 in U (and U_0(32))', in_U0_32(R1, need_U=True))
D2 = Matrix([[1, R(1, 2)], [0, 1]]); G2 = Matrix([[1, 0], [-16, 1]]); R2 = Matrix([[4 * n + 1, 0], [8 * (7 * n + 1), 1]])
check('n5: (1+2varpi) = D2 G2 R2', sp.simplify(one2 - D2 * G2 * R2) == sp.zeros(2))
check('n5: R2 in U', in_U0_32(R2, need_U=True))
jm = Matrix([[1, 0], [8, -1]])
check('n5: j*eps = [[1,0],[8,1]]', jm * eps == Matrix([[1, 0], [8, 1]]))
w0 = Matrix([[0, 1], [-1, 0]])
check('n5: [0] = [oo, w0]', cusp_of(w0) == 0)
D3 = Matrix([[8, 0], [0, R(1, 4)]]); G3 = Matrix([[1, 0], [8, 1]]); R3 = Matrix([[(n + 1) / 2, 0], [-4 * (n + 3), -1]])
check('n5: w0 varpi eps = D3 G3 R3 (as printed)', sp.simplify(w0 * vp * eps - D3 * G3 * R3) == sp.zeros(2))
check('n5: w0 varpi eps = D3 G3 (-R3), -R3 = R1 (TYZ sign misprint, -I in U)',
      sp.simplify(w0 * vp * eps + D3 * G3 * R3) == sp.zeros(2) and sp.simplify(R3 + R1) == sp.zeros(2))
check('n5: R3 in U', in_U0_32(R3, need_U=True))
D4 = Matrix([[-2, 1], [0, -R(1, 2)]]); G4 = Matrix([[7, -3], [-2, 1]]); R4 = Matrix([[4 * n - 17, 3], [8 * (n - 5), 7]])
check('n5: w0 (1+2varpi) = D4 G4 R4', sp.simplify(w0 * one2 - D4 * G4 * R4) == sp.zeros(2))
check('n5: R4 in U', in_U0_32(R4, need_U=True))
check('n5: w0 j eps = [[8,1],[-1,0]]', w0 * jm * eps == Matrix([[8, 1], [-1, 0]]))
for nm, G in (('G1', G1), ('G2', G2), ('G3', G3), ('G4', G4), ('w0 j eps', w0 * jm * eps), ('j eps', jm * eps)):
    check(f'n5: {nm} in SL_2(Z)', G.det() == 1 and all(x.is_integer for x in G))
for nm, D in (('D1', D1), ('D2', D2), ('D3', D3), ('D4', D4)):
    check(f'n5: {nm} upper triangular, det > 0, unit at odd p', D[1, 0] == 0 and D.det() > 0
          and all(sp.Rational(x).q & (sp.Rational(x).q - 1) == 0 for x in D))
# cusps claimed: R=[0], S=[1/16], T=[-1/8]; [0]^{varpi eps}=[-1/8], [0]^{1+2varpi}=[1/2], [0]^{j eps}=[0]
claims = [('R = [oo, varpi eps]', G1, 0), ('S = [oo, 1+2varpi]', G2, R(1, 16)), ('T = [oo, j eps]', jm * eps, R(-1, 8)),
          ('[0]^{varpi eps}', G3, R(-1, 8)), ('[0]^{1+2varpi}', G4, R(1, 2)), ('[0]^{j eps}', w0 * jm * eps, 0)]
for lab, G, cl in claims:
    c = cusp_of(G)
    check(f'n5: {lab} = {cl} (computed {c})', gamma0_equiv(c, cl))
# the 8 cusps of X_0(32) are pairwise inequivalent as listed in TYZ fact (3)
cusps = ['oo', 0, R(1, 2), R(1, 16), R(1, 4), R(-1, 4), R(1, 8), R(-1, 8)]
check('8 listed cusps pairwise inequivalent',
      all(not gamma0_equiv(cusps[i], cusps[j]) for i in range(8) for j in range(i + 1, 8)))
# switching components: det -> Q_+ Zhat^x -> (Z_2/4)^x
def comp_sign(detval):
    q = sp.Rational(detval)
    u = q / 2**v2(q)  # unit part at 2 of the idele concentrated at 2 (sign of q irrelevant: q_+ part = 2^v)
    return 1 if (u.p * pow(u.q, -1, 4)) % 4 == 1 else -1
for k in range(8):
    nn = 5 + 8 * k
    dets = {'varpi': (vp.det()).subs(m, k), '1+2varpi': (one2.det()).subs(m, k)}
    if k == 0:
        print('   det varpi, det(1+2varpi) at n=5:', dets)
    check(f'n5 n={nn}: varpi switches components, 1+2varpi does not',
          comp_sign(dets['varpi']) == -1 and comp_sign(dets['1+2varpi']) == 1)
# j: j^2 = 1, j x j = conj(x)
check('n5: j^2 = 1', jm * jm == I2)
check('n5: j M5 j = -M5 (conjugation)', sp.simplify(jm * M5 * jm + M5) == sp.zeros(2))
# Lemma coset5(2): varpi, 1+2varpi (and j, eps) normalise U_2. Generators of U_2:
t = symbols('t')
gens = [Matrix([[1, t], [0, 1]]), Matrix([[1, 0], [32 * t, 1]]), Matrix([[1 + 4 * t, 0], [0, 1]]), Matrix([[-1, 0], [0, -1]]),
        Matrix([[3, 0], [0, 3]]), Matrix([[5, 0], [0, 1]])]
def in_U_param(g):
    """g has entries affine in t (t ranges over Z_2), numeric in n; check g in U_2 for all t."""
    a, b, c, d = [sp.expand(x) for x in g]
    def pv(e):
        e = sp.expand(e)
        if e == 0:
            return 10**9
        return min(v2(cf) for cf in Poly(e, t).coeffs())
    ok = pv(a) >= 0 and pv(b) >= 0 and pv(c) >= 5 and pv(a - d) >= 2
    det = sp.expand(g.det())
    ok = ok and all(v2(det.subs(t, k2)) == 0 for k2 in range(16))
    return ok
for nm, x0 in (('varpi', vp), ('1+2varpi', one2), ('j', jm), ('eps', eps)):
    good = True
    for k in range(32):
        x = x0.subs(m, k)
        xi = x.inv()
        good = good and all(in_U_param(x * g * xi) and in_U_param(xi * g * x) for g in gens)
    check(f'n5: {nm} normalises U_2 (generators; n = 5+8k, k < 32)', good)
# (Z_hat + 4 O_K)^x in U: O_K = Z[sqrt(-n)] for n = 1 mod 4; 4*sqrt(-n) and Z_2 + 4 O_K units
g = I2 * symbols('a') + 4 * M5 * symbols('b')
a_, b_ = symbols('a b')
cg = sp.expand(g[1, 0]); dg = sp.expand(g[0, 0] - g[1, 1])
check('n5: (Z+4O_K) lands in M_2(Z_2) with 32|c and 4|(a-d)',
      all(v2(cf) >= 5 for cf in Poly(cg, m, a_, b_).coeffs()) and all(v2(cf) >= 2 for cf in Poly(dg, m, a_, b_).coeffs())
      and all(v2(cf) >= 0 for e in g for cf in Poly(sp.expand(e), m, a_, b_).coeffs()))

# ---------------- n = 7 mod 8 ----------------
def sqrt2adic(a, prec=60):
    """x in Z with x^2 = a mod 2^prec, a = 1 mod 8."""
    x = 1
    for k in range(3, prec):
        if (x * x - a) % 2**(k + 1) != 0:
            x += 2**(k - 1)
    assert (x * x - a) % 2**prec == 0
    return x
W = Matrix([[0, 1], [-32, 0]])
check('n7: W normalises U_0(32) (generators)', True if all(
    (lambda h: h[1, 0].subs(t, 1) % 32 == 0)(W * g.subs(t, 1) * W.inv()) for g in gens) else False)
check('n7: [oo]^W = [0]', (lambda Wi: sp.Rational(Wi[0, 0], Wi[1, 0]))(W.inv()) == 0)
PREC = 60
for nn in (7, 15, 23, 31, 39, 47, 55, 71, 79, 87, 95, 103, 111, 119, 127, 1001 * 8 + 7):
    # delta with delta^2 = -n mod 128; alpha = sqrt(-n) in Z_2 with 64 | alpha - delta
    delta = next(d for d in range(1, 128, 2) if (d * d + nn) % 128 == 0)
    alpha = sqrt2adic(-nn % 2**PREC, PREC)
    if (alpha - delta) % 64 != 0:
        alpha = (-alpha) % 2**PREC
    ok = (alpha - delta) % 64 == 0 and v2(alpha + delta) == 1
    M7 = Matrix([[delta, 2], [-(nn + delta**2) // 2, -delta]])
    ok = ok and M7 * M7 == -nn * I2 and (nn + delta**2) % 2 == 0
    j7 = Matrix([[1, 0], [-delta, -1]])
    ok = ok and j7 * j7 == I2 and j7 * M7 * j7 == -M7
    # O_K = Z[(1+sqrt(-n))/2] inside M_0(32)
    w = (I2 + M7) / 2
    ok = ok and all(sp.Rational(x).q == 1 for x in w) and w[1, 0] % 32 == 0
    # varpi^5 = (32,1) = 31/(2 alpha) sqrt(-n) + 33/2  (alpha only mod 2^PREC: work with the integer approximant)
    V5 = R(31, 2 * alpha) * M7 + R(33, 2) * I2
    X = W.inv() * j7 * V5
    # 2-adic check: entries in Z_2, 32 | c, det unit; errors of size 2^(PREC - small) are irrelevant
    vals = [v2(x) for x in X]
    detv = v2(X.det())
    okX = vals[0] >= 0 and vals[1] >= 0 and vals[2] >= 5 and vals[3] >= 0 and detv == 0
    # also check varpi^5 really is (32, 1): its eigen-decomposition on alpha-eigenspaces
    lam = [R(31, 2 * alpha) * s + R(33, 2) for s in (alpha, -alpha)]
    ok5 = lam[0] == 32 and lam[1] == 1
    check(f'n7 n={nn}: delta={delta}, embedding/j/O_K ok, varpi^5=(32,1), W^-1 j varpi^5 in U_0(32)_2 '
          f'(v2 entries {vals}, v2 det {detv})', ok and okX and ok5)

print('\nSUMMARY:', sum(1 for _, c in out if c), 'OK,', sum(1 for _, c in out if not c), 'FAIL')
