"""Geometry of the six-contact configuration C = {0,-15,-20,-24,-30,-60}.

(a) the identity G^6 - 97200 F^2 = H^2 and J = -57600 F^2/G^6;
(b) Moebius transformations permuting C (automorphisms of the branch configuration);
(c) the fifteen genus-one quotients y^2 = prod_{c in I}(u-c), |I| = 4: j-invariants and
    Frobenius traces, grouped into isogeny classes over Q (traces for p < 400);
(d) the genus-two quotient y^2 = F(u): L-polynomials at small primes, split test.
"""
from fractions import Fraction as Fr
from itertools import combinations, permutations
import sympy as sp

u = sp.symbols('u')
C = [0, -15, -20, -24, -30, -60]
F = sp.prod([u - c for c in C])
G = 7*u**2 + 300*u + 3600
H = (u**2 - 60*u - 1800)*(13*u**2 + 480*u + 3600)*(11*u**2 + 600*u + 7200)
print("(a) G^6 - 97200 F^2 - H^2 =", sp.expand(G**6 - 97200*F**2 - H**2))
J = -57600*F**2/G**6
print("    J - 1 numerator/denominator check, (J - (-16/27)):",
      sp.factor(sp.together(J + sp.Rational(16, 27))))

# (b) Moebius maps permuting C
def mob(a, b, c, d, x):
    if x is None:
        return None if c == 0 else Fr(a, 1) / c
    den = c * x + d
    return None if den == 0 else (a * x + b) / den

pts = [Fr(c) for c in C]
autos = []
for img in permutations(pts, 3):
    # Moebius sending pts[0],pts[1],pts[2] to img via cross-ratio
    z1, z2, z3 = pts[:3]
    w1, w2, w3 = img
    X = sp.symbols('X')
    Wv = sp.symbols('W')
    eq = sp.Eq((Wv - w1) * (w2 - w3) * (X - z2) * (z1 - z3), (Wv - w2) * (w1 - w3) * (X - z1) * (z2 - z3))
    sol = sp.solve(eq, Wv)
    if not sol:
        continue
    f = sp.simplify(sol[0])
    ok = True
    imgs = []
    for p in pts:
        v = f.subs(X, sp.Rational(p.numerator, p.denominator))
        if v.has(sp.zoo) or v not in [sp.Rational(q.numerator, q.denominator) for q in pts]:
            ok = False
            break
        imgs.append(v)
    if ok:
        autos.append((sp.factor(f), imgs))
print("(b) Moebius maps over Q permuting C:", len(autos))
for f, imgs in autos:
    print("   ", f, imgs)

# (c) genus-one quotients
primes = list(sp.primerange(7, 400))

def legendre(a, p):
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1

def trace_quartic(roots, p):
    # y^2 = prod (u - r), degree 4 monic: #affine = sum (1 + chi(f(u))); two points at infinity
    n = 0
    for x in range(p):
        v = 1
        for r in roots:
            v = v * (x - r) % p
        n += 1 + legendre(v, p)
    n += 2  # leading coefficient 1 is a square
    return p + 1 - n

def jinv_quartic(roots):
    a = sp.Poly(sp.prod([u - r for r in roots]), u).all_coeffs()  # a4 u^4 + ... + a0
    a4, a3, a2, a1, a0 = [sp.Integer(x) for x in a]
    I = 12 * a4 * a0 - 3 * a3 * a1 + a2**2
    Jv = 72 * a4 * a2 * a0 + 9 * a3 * a2 * a1 - 27 * a4 * a1**2 - 27 * a0 * a3**2 - 2 * a2**3
    return sp.nsimplify(6912 * I**3 / (4 * I**3 - Jv**2))

classes = {}
for I in combinations(C, 4):
    tr = tuple(trace_quartic(I, p) for p in primes)
    j = jinv_quartic(I)
    classes.setdefault(tr, []).append((I, j))
print("(c) 15 genus-one quotients fall into", len(classes), "Q-isogeny classes (traces p<400)")
for tr, members in classes.items():
    print("   traces a_7..a_31 =", tr[:8], " members:", [(m[0], m[1]) for m in members])

# (d) genus-two quotient y^2 = F(u)
def count_curve(p, k):
    # count points of y^2 = F(u) over F_{p^k}, k in {1,2}, sextic monic -> 2 points at infinity
    if k == 1:
        n = 0
        for x in range(p):
            v = 1
            for r in C:
                v = v * (x - r) % p
            n += 1 + legendre(v, p)
        return n + 2
    # F_{p^2} = F_p[s]/(s^2 - nr), nr a nonresidue
    nr = next(a for a in range(2, p) if legendre(a, p) == -1)
    def mul(x, y):
        return ((x[0] * y[0] + nr * x[1] * y[1]) % p, (x[0] * y[1] + x[1] * y[0]) % p)
    def pw(x, e):
        r = (1, 0)
        while e:
            if e & 1:
                r = mul(r, x)
            x = mul(x, x)
            e >>= 1
        return r
    q = p * p
    n = 0
    for a0 in range(p):
        for a1 in range(p):
            v = (1, 0)
            for r in C:
                v = mul(v, ((a0 - r) % p, a1))
            if v == (0, 0):
                n += 1
            else:
                n += 2 if pw(v, (q - 1) // 2) == (1, 0) else 0
    return n + 2

print("(d) genus-two quotient y^2 = F(u):")
T = sp.symbols('T')
for p in [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]:
    N1 = count_curve(p, 1)
    N2 = count_curve(p, 2)
    s1 = p + 1 - N1
    s2 = p * p + 1 - N2
    # L(T) = 1 - a1 T + a2 T^2 - p a1 T^3 + p^2 T^4, with a1 = s1, a2 = (s1^2 - s2)/2
    a1 = s1
    a2 = (s1 * s1 - s2) // 2
    L = 1 - a1 * T + a2 * T**2 - p * a1 * T**3 + p**2 * T**4
    print("   p=%d  L(T)=%s  factor over Q: %s" % (p, sp.expand(L), sp.factor(L)))
