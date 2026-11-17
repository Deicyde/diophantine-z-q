"""mcheck-appF s2: Weil indices, Hilbert symbols and the operator relations of App F (tex L8625-8960).

The Weil index gamma_v(a) of x -> psi_v(a x^2) is computed numerically as the phase of the
Gauss integral over a large ball, with psi_p(t) = exp(-2 pi i {t}_p) and psi_oo(t) = exp(2 pi i t)
as in L8642-8643. The identities proved in the tex are then tested at v = 2, 3, 5, 7, oo.
Negative controls (NEG) must fail.
"""
import cmath
import math
import random
from fractions import Fraction

random.seed(8625)
results = []


def check(name, ok, info=""):
    results.append((name, bool(ok)))
    print(("PASS " if ok else "FAIL ") + name + ((" : " + str(info)) if info else ""))


def neg(name, claim_value, info=""):
    check("NEG " + name + " (wrong input must fail)", not claim_value, info)


def vp(x, p):
    x = Fraction(x)
    if x == 0:
        return 10**9
    n, d, k = x.numerator, x.denominator, 0
    while n % p == 0:
        n //= p
        k += 1
    while d % p == 0:
        d //= p
        k -= 1
    return k


def unit_part(x, p):
    x = Fraction(x)
    return x / Fraction(p) ** vp(x, p)


def frac_p(t, p):
    """{t}_p for t in Q: the p-power-denominator fractional part."""
    t = Fraction(t)
    k = vp(t.denominator, p)
    if k <= 0:
        return Fraction(0)
    pk = p**k
    rest = t.denominator // pk
    # t = n/(pk*rest); {t}_p = (n * rest^{-1} mod pk)/pk
    return Fraction((t.numerator * pow(rest, -1, pk)) % pk, pk)


SIGN = -1  # psi_p(t) = exp(SIGN * 2 pi i {t}_p), the tex convention


def psi_p(t, p):
    return cmath.exp(SIGN * 2j * math.pi * float(frac_p(t, p)))


def gamma_p(a, p, extra=0):
    a = Fraction(a)
    k = vp(a, p)
    # the shell p^{-n-1}Z_p - p^{-n}Z_p contributes 0 once 2n >= k + 2 (odd p) or k + 4 (p = 2)
    n = -((-(k + (4 if p == 2 else 2))) // 2) + extra
    M = max(2 * n - k, 1)  # a y^2 p^{-2n} mod Z_p depends only on y mod p^M
    s = 0
    for y in range(p**M):
        s += psi_p(a * y * y / Fraction(p) ** (2 * n), p)
    return s / abs(s)


_cache = {}


def gamma(a, v):
    a = Fraction(a)
    if v == "oo":
        return cmath.exp(1j * math.pi / 4 * (1 if a > 0 else -1))
    key = (a, v, SIGN)
    if key not in _cache:
        _cache[key] = gamma_p(a, v)
    return _cache[key]


def hilbert(a, b, v):
    a, b = Fraction(a), Fraction(b)
    if v == "oo":
        return -1 if (a < 0 and b < 0) else 1
    p = v
    al, be = vp(a, p), vp(b, p)
    u, w = unit_part(a, p), unit_part(b, p)
    u = u.numerator * pow(u.denominator, -1, 8 if p == 2 else p) % (8 if p == 2 else p)
    w = w.numerator * pow(w.denominator, -1, 8 if p == 2 else p) % (8 if p == 2 else p)
    if p != 2:
        def leg(x):
            return 1 if pow(x % p, (p - 1) // 2, p) == 1 else -1
        e = (-1) ** (al * be * ((p - 1) // 2))
        return e * leg(u) ** be * leg(w) ** al
    eps = lambda x: ((x - 1) // 2) % 2
    om = lambda x: ((x * x - 1) // 8) % 2
    return (-1) ** ((eps(u) * eps(w) + al * om(w) + be * om(u)) % 2)


def close(z, w, tol=1e-7):
    return abs(z - w) < tol


PLACES = [2, 3, 5, 7, "oo"]


def rand_rat(v=None):
    sgn = random.choice([1, -1])
    num = random.choice([1, 2, 3, 5, 6, 7, 10, 11, 13, 14, 15, 21, 30])
    den = random.choice([1, 1, 2, 3, 5, 7])
    return Fraction(sgn * num, den)


check("sanity: Gauss phase stable when the ball is enlarged", all(close(gamma_p(a, p), gamma_p(a, p, 1)) for p in (2, 3, 5, 7) for a in (1, 3, Fraction(1, 2), Fraction(5, 7), 14, -3)))
# sanity: gamma(1) at 2 is exp(-i pi/4) in this convention (product formula with oo)
check("sanity gamma_2(1) * gamma_oo(1) = 1", close(gamma(1, 2) * gamma(1, "oo"), 1), gamma(1, 2))

# W1: gamma(ua)/gamma(a) = gamma(u)/gamma(1) (u,a)  (L8689, L8705-8716)
ok = True
bad = False
for trial in range(250):
    v = random.choice(PLACES)
    u, a = rand_rat(), rand_rat()
    lhs = gamma(u * a, v) / gamma(a, v)
    rhs = gamma(u, v) / gamma(1, v) * hilbert(u, a, v)
    ok &= close(lhs, rhs)
    if not close(lhs, gamma(u, v) / gamma(1, v)):
        bad = True
check("L8689/L8716 gamma(ua)/gamma(a) = gamma(u)/gamma(1) (u,a)_v, v in {2,3,5,7,oo}", ok)
neg("same identity without the Hilbert symbol", not bad)

# W2-W3: gamma(1)^4 = (-1,-1); gamma(Q)^2 = (det Q,-1) gamma(1)^6 for diagonal ternary Q (L8761-8768)
ok2 = all(close(gamma(1, v) ** 4, hilbert(-1, -1, v)) for v in PLACES)
check("L8762 gamma(1)^4 = (-1,-1)_v", ok2)
neg("gamma(1)^4 = 1 at v=2", close(gamma(1, 2) ** 4, 1))
ok = True
for trial in range(150):
    v = random.choice(PLACES)
    a = [rand_rat() for _ in range(3)]
    gQ = gamma(a[0], v) * gamma(a[1], v) * gamma(a[2], v)
    ok &= close(gQ**2, hilbert(a[0] * a[1] * a[2], -1, v) * gamma(1, v) ** 6)
    ok &= close(gQ**4, hilbert(-1, -1, v))  # W_Q^2 = (-1,-1) M_Q(-1)
check("L8761 gamma(Q)^2 = (det Q,-1) gamma(1)^6 and gamma(Q)^4 = (-1,-1) (W_Q^2 relation)", ok)

# W4-W5: r_Q(a) r_Q(b) = (a,b) r_Q(ab); r_Q(u)/r_Q0(u) = (u, det Q) (L8763, L8808-8811, (O.5a))
def rQ(Q, a, v):
    num = 1
    den = 1
    for q in Q:
        num *= gamma(a * q, v)
        den *= gamma(q, v)
    return num / den


ok = True
okq = True
okneg = True
for trial in range(150):
    v = random.choice(PLACES)
    Q = [rand_rat() for _ in range(3)]
    a, b = rand_rat(), rand_rat()
    ok &= close(rQ(Q, a, v) * rQ(Q, b, v), hilbert(a, b, v) * rQ(Q, a * b, v))
    detQ = Q[0] * Q[1] * Q[2]
    okq &= close(rQ(Q, a, v) / rQ([1, 1, 1], a, v), hilbert(a, detQ, v))
    if not close(rQ(Q, a, v) / rQ([1, 1, 1], a, v), 1):
        okneg = False
check("L8763 r_Q(a) r_Q(b) = (a,b) r_Q(ab)", ok)
check("L8809/(O.5a) r_Q(u)/r_Q0(u) = (u, det Q)", okq)
neg("r_Q(u)/r_Q0(u) = 1 (no determinant character)", okneg)

# W6: last operator relation scalar gamma(Q)^2 gamma(bQ)^2 = (-b,-1) (L8781-8783)
ok = True
for trial in range(150):
    v = random.choice(PLACES)
    Q = [rand_rat() for _ in range(3)]
    b = rand_rat()
    gQ = gamma(Q[0], v) * gamma(Q[1], v) * gamma(Q[2], v)
    gbQ = gamma(b * Q[0], v) * gamma(b * Q[1], v) * gamma(b * Q[2], v)
    ok &= close(gQ**2 * gbQ**2, hilbert(-b, -1, v))
check("L8781-8783 gamma(Q)^2 gamma(bQ)^2 = (-b,-1)_v", ok)

# W7: product formula prod_v gamma_v(a) = 1 (Weil II.30 Prop 5, used L8998-9002)
def gamma_all(a):
    a = Fraction(a)
    primes = {2}
    for x in (a.numerator, a.denominator):
        x = abs(x)
        q = 2
        while q * q <= x:
            while x % q == 0:
                primes.add(q)
                x //= q
            q += 1
        if x > 1:
            primes.add(x)
    r = gamma(a, "oo")
    for p in primes:
        r *= gamma(a, p)
    return r


okp = all(close(gamma_all(a), 1) for a in [1, -1, 2, 3, -3, 5, -7, Fraction(3, 5), 6, -15, 11, Fraction(-7, 2)])
check("L8999 product formula prod_v gamma_v(a) = 1 (sample of rationals)", okp)
SIGN = +1
_cache.clear()
neg("product formula with psi_p(t) = exp(+2 pi i {t}_p) (inconsistent with psi_oo)", all(close(gamma_all(a), 1) for a in [1, 3, -7]))
SIGN = -1
_cache.clear()

# W8: (O.5c) prod_{p | 2m} (d,m)_p = (m/d) for d > 0 prime to 2m (L8903-8910)
def jacobi(a, n):
    a %= n
    r = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                r = -r
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            r = -r
        a %= n
    return r if n == 1 else 0


def pf(x):
    s = set()
    q = 2
    while q * q <= x:
        while x % q == 0:
            s.add(q)
            x //= q
        q += 1
    if x > 1:
        s.add(x)
    return s


ok = True
okneg = True
for m in (3, 7, 11, 15, 19, 23, 35, 39, 43, 55, 59, 3 * 7 * 11):
    for d in range(1, 300, 2):
        if math.gcd(d, m) > 1:
            continue
        prod = 1
        for p in pf(2 * m):
            prod *= hilbert(d, m, p)
        ok &= prod == jacobi(m, d)
        prod_odd = 1
        for p in pf(m):
            prod_odd *= hilbert(d, m, p)
        if prod_odd != jacobi(m, d):
            okneg = False
        # explicit local factors (L8885-8890)
        if m % 4 == 3:
            ok &= hilbert(d, m, 2) == (-1) ** ((d - 1) // 2)
        for p in pf(m):
            ok &= hilbert(d, m, p) == jacobi(d, p) ** vp(m, p)
check("L8885-8910 (O.5c) prod_{p|2m}(d,m)_p = (m/d); (u,m)_2 = (-1)^{(u-1)/2}; (u,m)_p = (u/p)^{v_p m}", ok)
neg("(O.5c) with the dyadic factor dropped", okneg)
check("L8890 (u,m)_2 trivial on 1+4Z_2 for m = 3 mod 4", all(hilbert(u, m, 2) == 1 for u in range(1, 200, 4) for m in (3, 7, 11, 19)))

# W9: finite-field model of the operator identities (rank one; the ternary case is a tensor product).
# Functions on F_p; U(b) phi(x) = e(b a x^2 / p) phi(x); D(c) phi(x) = phi(c x); F phi(y) = p^{-1/2} sum phi(x) e(2 a x y / p).
def e(t, p):
    return cmath.exp(2j * math.pi * (t % p) / p)


def opU(b, a, p):
    return [[e(b * a * x * x, p) if x == y else 0 for y in range(p)] for x in range(p)]


def opD(c, p):
    # (D phi)(x) = phi(c x): matrix row x has 1 at column c x
    return [[1 if y == (c * x) % p else 0 for y in range(p)] for x in range(p)]


def opF(a, p):
    return [[e(2 * a * x * y, p) / math.sqrt(p) for y in range(p)] for x in range(p)]  # row = output y? use symmetric


def mm(A, B):
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def inv_unitary(A):
    n = len(A)
    return [[A[j][i].conjugate() if isinstance(A[j][i], complex) else A[j][i] for j in range(n)] for i in range(n)]


def gauss(c, p):
    s = sum(e(c * x * x, p) for x in range(p)) / math.sqrt(p)
    return s


def mclose(A, B):
    return all(abs(A[i][j] - B[i][j]) < 1e-8 for i in range(len(A)) for j in range(len(A)))


ok = True
okneg = True
for p in (5, 7, 11, 13):
    for a in (1, 2, 3):
        for b in range(1, p):
            if a % p == 0:
                continue
            bi = pow(b, -1, p)
            F = opF(a, p)
            Fi = inv_unitary(F)
            lhs = mm(mm(F, opU(b, a, p)), F)
            core = mm(mm(mm(opU(-bi, a, p), opD(bi, p)), Fi), opU(-bi, a, p))
            g = gauss(b * a, p)
            ok &= mclose(lhs, [[g * z for z in row] for row in core])
            if mclose(lhs, [[g.conjugate() * z for z in row] for row in core]) and abs(g - g.conjugate()) > 1e-6:
                okneg = False
check("L8752-8755 finite model: F U(b) F = gamma(bQ) U(-1/b) D(1/b) F^{-1} U(-1/b) (rank one, p=5..13)", ok)
neg("same identity with the conjugate Gauss phase", not okneg)

# W10: real place, rank one, Q(x)=x^2, Gaussian test function, numerical integration (L8746-8749)
def integrate(f, L=12.0, N=24000):
    h = 2 * L / N
    return sum(f(-L + (i + 0.5) * h) for i in range(N)) * h


def Fq(phi):
    # F_Q phi(y) = int phi(x) e(B_Q(x,y)) |det 2A|^{1/2} dx with B_Q = 2xy, |2|^{1/2}
    return lambda y: math.sqrt(2) * integrate(lambda x: phi(x) * cmath.exp(2j * math.pi * 2 * x * y))


phi = lambda x: math.exp(-math.pi * x * x)
okr = True
for b in (0.7, -1.3, 2.0):
    for vv in (0.0, 0.31, -0.55):
        # LHS of the Fourier formula: int e(b z^2 + 2 z v) |2|^{1/2} dz, regularised by the Gaussian factor e^{-eps z^2}
        eps = 1e-3
        lhs = math.sqrt(2) * integrate(lambda z: cmath.exp(2j * math.pi * (b * z * z + 2 * z * vv)) * math.exp(-eps * z * z), L=60.0, N=240000)
        rhs = abs(b) ** -0.5 * gamma(Fraction(b).limit_denominator(100), "oo") * cmath.exp(-2j * math.pi * vv * vv / b) / math.sqrt(2) * math.sqrt(2)
        # exact value of the rank-one Fresnel integral: int e(b z^2 + 2 z v) dz = |2b|^{-1/2}... with measure |2|^{1/2} dz:
        # sqrt2 * |b|^{-1/2} e^{i pi sgn b/4} e(-v^2/b) / sqrt2 = |b|^{-1/2} gamma(b) e(-v^2/b)  (rank one: |b|^{-1/2})
        okr &= abs(lhs - rhs) < 2e-2
check("L8746-8749 real rank-one Fourier formula: int e(bQ(z)+B_Q(z,v)) dz_Q = |b|^{-1/2} gamma(bQ) e(-Q(v)/b)", okr)
neg("same with gamma(bQ) replaced by its inverse at b=0.7", abs(math.sqrt(2) * integrate(lambda z: cmath.exp(2j * math.pi * (0.7 * z * z)) * math.exp(-1e-3 * z * z), L=60.0, N=240000)
                                                              - 0.7 ** -0.5 / gamma(1, "oo")) < 2e-2)

npass = sum(ok for _, ok in results)
print("\n%d/%d PASS" % (npass, len(results)))
