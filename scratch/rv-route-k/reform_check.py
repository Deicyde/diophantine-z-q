"""Exact checks of the reformulation of Phi for both pole polynomials.

Congruent version Q_pole^C:  T1 = A(A-e)(A+e),  T2 = A(Az^2-eH)(Az^2+eH).
Manuscript version Q_pole :  T1 = A(A-e)(A+3e), T2 = A(Az^2-eH)(Az^2+3eH).

(1) Parametrizations of {l : the curve has a point with x = beta}:
    C_l : l(tau) = beta(beta - tau^2)/(beta + tau^2),  y = 2 beta^2 tau/(beta + tau^2);
    E_l : l(t)   = beta(beta t^2 - 1)/(beta t^2 + 3)   (the note's formula), y computed.
(2) Inverse map for C: tau = y/(beta + l) recovers tau from any point (beta, y) on C_l.
(3) Witness construction: from (m, tau1, tau2) with theta*g(tau1)*g(tau2) a square build all
    eleven witnesses and check Q_pole^C = 0 exactly, on examples found by a small search.
"""
import itertools
from fractions import Fraction as Fr
from math import isqrt


def is_sq(r):
    r = Fr(r)
    if r < 0:
        return False
    n, d = r.numerator, r.denominator
    return isqrt(n) ** 2 == n and isqrt(d) ** 2 == d


def sqrtQ(r):
    r = Fr(r)
    return Fr(isqrt(r.numerator), isqrt(r.denominator))


def sqf(n):
    n = int(n)
    s = -1 if n < 0 else 1
    n = abs(n)
    out = 1
    p = 2
    while p * p <= n:
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        if e % 2:
            out *= p
        p += 1
    return s * out * n


def sqfQ(r):
    r = Fr(r)
    return sqf(r.numerator * r.denominator)


def m_of(b):
    return (1 - 2 * b[0]) * (1 + b[1]) * (1 + 2 * b[2]) * (1 + 4 * b[3]) * (1 + 6 * b[4]) * (1 + 12 * b[5])


def Qpole(B, b, e, z, r1, r2, w, c):
    """c = 1 (congruent) or 3 (manuscript)."""
    m = m_of(b)
    A = m * B
    H = A * (A - B ** 2)
    T1 = A * (A - e) * (A + c * e)
    T2 = A * (A * z ** 2 - e * H) * (A * z ** 2 + c * e * H)
    return B * (sum((bi ** 2 - bi) ** 2 for bi in b) + (e * H * z * w - 1) ** 2 + (r1 ** 2 - T1) ** 2
                + (r2 ** 2 - T2) ** 2)


def bits_of(m):
    for b in itertools.product([0, 1], repeat=6):
        if m_of(b) == m:
            return list(b)
    raise ValueError(m)


# (1), (2)
cnt = 0
for beta in [2, 3, 5, -6, 17, 41, -105]:
    for tn in range(-6, 7):
        for td in range(1, 6):
            tau = Fr(tn, td)
            if beta + tau ** 2 == 0:
                continue
            l = beta * (beta - tau ** 2) / (beta + tau ** 2)
            y = 2 * Fr(beta) ** 2 * tau / (beta + tau ** 2)
            assert y ** 2 == beta * (beta - l) * (beta + l)
            if l != 0 and beta + l != 0:
                assert y / (beta + l) == tau
            # E family (note's formula)
            t = tau
            if beta * t * t + 3 != 0:
                lE = beta * (beta * t * t - 1) / (beta * t * t + 3)
                assert is_sq(beta * (beta - lE) * (beta + 3 * lE)), (beta, t)
            cnt += 1
print("parametrization identities checked:", cnt)


# (3) witnesses for the congruent polynomial
def lC(beta, tau):
    if tau is None:
        return Fr(-beta), Fr(0)  # tau = infinity: point (beta, 0) on C_{-beta}
    return beta * (beta - tau ** 2) / (beta + tau ** 2), 2 * Fr(beta) ** 2 * tau / (beta + tau ** 2)


def witnesses_C(B, m, tau1, tau2):
    A = m * B
    beta = sqfQ(A)
    X2 = A / beta  # A = beta X^2
    assert is_sq(X2)
    X = sqrtQ(X2)
    l1, y1 = lC(beta, tau1)
    if l1 == 0:
        return None
    e = l1 * X2
    r1 = y1 * X ** 3
    H = A * (A - B ** 2)
    l2, y2 = lC(beta, tau2)
    if l2 == 0 or H == 0:
        return None
    lam2 = e * H / l2
    z2 = beta * lam2 / A
    if not is_sq(z2):
        return None
    z = sqrtQ(z2)
    lam = sqrtQ(lam2)  # lam2 = A z^2 / beta is a square since z2 and A/beta are
    r2 = y2 * lam ** 3 / z
    w = 1 / (e * H * z)
    return bits_of(m), e, z, r1, r2, w


found = 0
taus = [None] + sorted({Fr(a, b) for a in range(-5, 6) for b in range(1, 5)})
divs = [s * d for d in [1, 2, 3, 5, 6, 7, 10, 13, 14, 15, 21, 26, 30, 35, 39, 42] for s in (1, -1)]
for beta in [5, 6, 7, 17, 41, 105]:
    gvals = {}
    for tau in taus:
        if tau is None:
            g = -beta
        else:
            if beta + tau ** 2 == 0:
                continue
            g = beta * (beta - tau ** 2) * (beta + tau ** 2)
        if g != 0:
            gvals[tau] = g
    for (t1, g1), (t2, g2) in itertools.product(gvals.items(), repeat=2):
        theta = abs(sqfQ(Fr(g1) * g2))
        if theta == 1:
            continue
        # need B with sqf(mB) = beta, sqf(m(m-B)) = theta: m^2 = beta X^2 + theta Y^2
        for m in divs:
            if sqf(m * beta) == 0:
                continue
            hit = None
            for Yn in range(0, 30):
                for Yd in range(1, 12):
                    Y = Fr(Yn, Yd)
                    X2 = (Fr(m) ** 2 - theta * Y ** 2) / beta
                    if X2 > 0 and is_sq(X2):
                        B = beta * X2 / m
                        if B != 0 and B != m and sqfQ(m * B) == beta:
                            hit = B
                            break
                if hit is not None:
                    break
            if hit is None:
                continue
            B = hit
            W = witnesses_C(B, m, t1, t2)
            if W is None:
                continue
            b, e, z, r1, r2, w = W
            val = Qpole(B, [Fr(x) for x in b], e, z, r1, r2, w, 1)
            assert val == 0, (B, m, t1, t2)
            found += 1
            if found <= 5:
                print("zero of Q_pole^C: B =", B, "m =", m, "beta =", beta, "theta =", theta,
                      "tau =", t1, t2, "e =", e, "z =", z)
            break
        if found >= 40:
            break
print("explicit zeros of Q_pole^C built and checked exactly:", found)

# theta = 1 trivial case: 2-torsion witnesses, both polynomials
for B, m in [(Fr(7, 16), 1), (Fr(15, 32), 2)]:
    A = m * B
    H = A * (A - B ** 2)
    c2 = m * (m - B)
    if is_sq(c2):
        c = sqrtQ(c2)
        for cc in (1, 3):
            val = Qpole(B, [Fr(x) for x in bits_of(m)], A, B * c, Fr(0), Fr(0), 1 / (A * H * B * c), cc)
            valnote = Qpole(B, [Fr(x) for x in bits_of(m)], A, c, Fr(0), Fr(0), 1 / (A ** 3 * c ** 3), cc)
            print("   with the note's z = c, w = (A^3 c^3)^-1 the value is", valnote)
            print("theta=1 example B =", B, "m =", m, "c =", c, "Q_pole value (coef", cc, "):", val)
