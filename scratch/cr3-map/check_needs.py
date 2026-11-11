"""Exact checks for map-needs.md (standard library only, < 30 inputs per check).

1. Quartic form of Loc: a point (x, y) on C_d with x = beta*s^2 gives w = y/s with
   w^2 = beta*(beta^2 s^4 - d^2); checked on points built from the tau-parametrization.
2. Phi(B) from (m, tau1, tau2) with theta*l(tau1)*l(tau2) in +-Q^2: build the eleven witnesses
   exactly as in RouteK/Assembly/Points.lean (poleSoluble_of_points) and evaluate polePoly.
3. Generalized multiplier: v_p(H) parity for H = A(A - B^2), A = mB, v_p(B) < 0 odd,
   for v_p(m) even >= 0 (always odd) and a v_p(m) even < 0 counterexample.
"""
from fractions import Fraction as Fr
from math import isqrt
import itertools, random


def factor(n):
    n = abs(n); f = {}; d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1; n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def sqf_int(n):
    s = 1 if n > 0 else -1
    r = 1
    for p, e in factor(n).items():
        if e % 2:
            r *= p
    return s * r


def sqf(x):
    x = Fr(x)
    return sqf_int(x.numerator * x.denominator)


def is_sq(x):
    x = Fr(x)
    if x < 0:
        return False
    a, b = x.numerator, x.denominator
    return isqrt(a) ** 2 == a and isqrt(b) ** 2 == b


def sqrt_q(x):
    x = Fr(x)
    return Fr(isqrt(x.numerator), isqrt(x.denominator))


def ell(beta, tau):  # rv-route-k 4.2: C_l has the point x = beta
    return Fr(beta) * (beta - tau ** 2) / (beta + tau ** 2)


def yy(beta, tau):
    return Fr(2 * beta * beta) * tau / (beta + tau ** 2)


def pole_poly(B, b, e, z, r1, r2, w):
    m = (1 - 2 * b[0]) * (1 + b[1]) * (1 + 2 * b[2]) * (1 + 4 * b[3]) * (1 + 6 * b[4]) * (1 + 12 * b[5])
    A = m * B
    H = A * (A - B ** 2)
    T1 = A * (A - e) * (A + e)
    T2 = A * (A * z ** 2 - e * H) * (A * z ** 2 + e * H)
    return B * (sum((bi ** 2 - bi) ** 2 for bi in b) + (e * H * z * w - 1) ** 2
                + (r1 ** 2 - T1) ** 2 + (r2 ** 2 - T2) ** 2)


def bits_of(m):
    k = abs(m)
    bits = [Fr(1 if m < 0 else 0)] + [Fr(1 if k % p == 0 else 0) for p in (2, 3, 5, 7, 13)]
    return bits


def check1():
    random.seed(1)
    n = 0
    for _ in range(12):
        beta = random.choice([-7, 7, 15, -15, 23, 31, -39, 55])
        tau = Fr(random.randint(-9, 9), random.randint(1, 7))
        if tau == 0:
            continue
        d, x, y = ell(beta, tau), Fr(beta), yy(beta, tau)
        assert y ** 2 == x ** 3 - d ** 2 * x
        s = Fr(1)
        w = y / s
        assert w ** 2 == beta * (beta ** 2 * s ** 4 - d ** 2)
        n += 1
    print("check1 quartic form: ok on", n, "points")


def witnesses(B, m, tau1, tau2):
    """Return the eleven witnesses or None (Points.lean recipe)."""
    beta, theta = sqf(m * B), sqf(m * (m - B))
    N = ell(beta, tau1)                       # C_N has (beta, y1)
    x1, y1 = Fr(beta), yy(beta, tau1)
    # need N*theta = +- l(tau2) * k^2
    l2 = ell(beta, tau2)
    ratio = N * theta / l2
    if not is_sq(abs(ratio)):
        return None
    k = sqrt_q(abs(ratio))
    x2, y2 = Fr(beta) * k ** 2, yy(beta, tau2) * k ** 3     # point on C_{l2 k^2} = C_{N theta}
    assert y2 ** 2 == x2 ** 3 - (N * theta) ** 2 * x2
    t = sqrt_q(m * B / beta)
    c = sqrt_q(m * (m - B) / theta)
    s, s2 = Fr(1), k
    h = B * c
    e = N * (t / s) ** 2
    z = s2 * h / s
    H = theta * h ** 2
    r1 = y1 * (t / s) ** 3
    r2 = y2 * (t * h / s) ** 3 / z
    w = 1 / (e * H * z)
    return bits_of(m), e, z, r1, r2, w


def check2():
    found = 0
    tries = 0
    smalls = sorted({Fr(a, b) for a in range(-6, 7) for b in range(1, 5) if a != 0})
    cases = [(Fr(5, 162), 2)] + [(Fr(a, b), m) for (a, b, m) in
             [(1, 9, 1), (2, 25, 1), (3, 49, 2), (1, 16, 3), (5, 36, 1), (7, 81, 2), (1, 50, 5)]]
    for B, m in cases:
        tries += 1
        beta, theta = sqf(m * B), sqf(m * (m - B))
        hit = None
        for t1, t2 in itertools.product(smalls, smalls):
            if beta + t1 ** 2 == 0 or beta + t2 ** 2 == 0 or ell(beta, t1) == 0 or ell(beta, t2) == 0:
                continue
            if is_sq(abs(theta * ell(beta, t1) * ell(beta, t2))):
                hit = (t1, t2); break
        if hit is None:
            print("  B=%s m=%d beta=%d theta=%d: no (tau1,tau2) of small height" % (B, m, beta, theta))
            continue
        wt = witnesses(B, m, *hit)
        assert wt is not None
        b, e, z, r1, r2, w = wt
        val = pole_poly(B, b, e, z, r1, r2, w)
        assert val == 0, val
        found += 1
        print("  B=%s m=%d beta=%d theta=%d taus=%s: polePoly = 0" % (B, m, beta, theta, hit))
    print("check2 Phi from (m,tau1,tau2):", found, "of", tries, "inputs certified exactly")


def vp(x, p):
    x = Fr(x)
    if x == 0:
        return None
    v = 0
    a, b = x.numerator, x.denominator
    while a % p == 0:
        a //= p; v += 1
    while b % p == 0:
        b //= p; v -= 1
    return v


def check3():
    p = 331
    random.seed(3)
    ok = 0
    for _ in range(20):
        bexp = -random.choice([1, 3, 5])
        jexp = random.choice([0, 1, 2])
        B = Fr(random.randint(1, 300), random.randint(1, 300)) * Fr(p) ** bexp
        if vp(B, p) != bexp:
            continue
        m = random.choice([1, -3, 10, 2730]) * Fr(p) ** (2 * jexp)
        A = m * B
        H = A * (A - B ** 2)
        assert vp(H, p) % 2 == 1 and vp(H, p) == 3 * bexp + 2 * jexp
        ok += 1
    # counterexample: v_p(m) = -2j with j > -b/2 ... take b = -1, v_p(m) = -2
    B = Fr(1, p); m = Fr(1, p ** 2)
    A = m * B; H = A * (A - B ** 2)
    print("check3 v_p(H) = 3b + 2j odd for v_p(m) = 2j >= 0:", ok, "cases;",
          "counterexample v_p(m) = -2, v_p(B) = -1: v_p(A) =", vp(A, p), "v_p(H) =", vp(H, p))


if __name__ == "__main__":
    check1(); check2(); check3()
