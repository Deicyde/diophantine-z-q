"""Search for pole witnesses via the reformulation

  Phi(B)  <=>  exists signed m | 2730 and t1, t2 in P^1(Q) with
               theta * g(t1) * g(t2) a square,

where beta = sqf(mB), theta = sqf(m(m - B)), g(t) = beta(beta t^2 - 1)(beta t^2 + 3).
For each solution the eleven witnesses are built explicitly and Q_pole is evaluated
exactly (Fractions), so every reported solution is an exact certificate.

Usage: python phi_search.py [num_samples] [height_bound] [seed]
"""
import sys
import random
from fractions import Fraction as F
from math import gcd, isqrt
import cypari2

pari = cypari2.Pari()
pari.allocatemem(2 * 10**9)


def core(n):
    """Signed squarefree part of a nonzero rational n (as an int)."""
    n = F(n)
    return int(pari.core(int(n.numerator) * int(n.denominator)))


def is_square(q):
    q = F(q)
    if q < 0:
        return False
    a, b = q.numerator, q.denominator
    return isqrt(a) ** 2 == a and isqrt(b) ** 2 == b


def sqrt_q(q):
    q = F(q)
    return F(isqrt(q.numerator), isqrt(q.denominator))


def pole_poly(B, b, e, z, r1, r2, w):
    m = (1 - 2 * b[0]) * (1 + b[1]) * (1 + 2 * b[2]) * (1 + 4 * b[3]) * (1 + 6 * b[4]) * (1 + 12 * b[5])
    A = m * B
    H = A * (A - B * B)
    T1 = A * (A - e) * (A + 3 * e)
    T2 = A * (A * z * z - e * H) * (A * z * z + 3 * e * H)
    return B * (sum((x * x - x) ** 2 for x in b) + (e * H * z * w - 1) ** 2
                + (r1 * r1 - T1) ** 2 + (r2 * r2 - T2) ** 2)


FACTORS = [(-1, 0), (2, 1), (3, 2), (5, 3), (7, 4), (13, 5)]


def bits_of_m(m):
    """Witnesses b_0..b_5 in {0,1} realizing the signed divisor m of 2730."""
    b = [0] * 6
    if m < 0:
        b[0] = 1
        m = -m
    for p, i in FACTORS[1:]:
        if m % p == 0:
            b[i] = 1
            m //= p
    assert m == 1
    return [F(x) for x in b]


def n_of_t(beta, t):
    """n with the point (beta, y) on E_n: n = beta(beta t^2 - 1)/(beta t^2 + 3); t=None is infinity."""
    if t is None:
        return F(beta)
    return F(beta) * (beta * t * t - 1) / (beta * t * t + 3)


def witnesses(B, m, t1, t2):
    """Build (b, e, z, r1, r2, w) from a solution, or None if a guard fails."""
    A = m * B
    H = A * (A - B * B)
    beta = core(A)
    lam2 = A / beta
    assert is_square(lam2)
    lam = sqrt_q(lam2)
    n1, n2 = n_of_t(beta, t1), n_of_t(beta, t2)
    e = n1 * lam2
    y1sq = F(beta) * (beta - n1) * (beta + 3 * n1)
    if not is_square(y1sq):
        return None
    r1 = sqrt_q(y1sq) * lam ** 3
    mu2 = e * H / n2
    if not is_square(mu2) or mu2 == 0:
        return None
    mu = sqrt_q(mu2)
    y2sq = F(beta) * (beta - n2) * (beta + 3 * n2)
    if not is_square(y2sq):
        return None
    z = mu / lam
    r2 = sqrt_q(y2sq) * mu ** 3 / z
    if e * H * z == 0:
        return None
    w = 1 / (e * H * z)
    return bits_of_m(m), e, z, r1, r2, w


def small_t(bound):
    yield None
    for b in range(1, bound + 1):
        for a in range(-bound, bound + 1):
            if gcd(a, b) == 1:
                yield F(a, b)


def search(B, bound):
    """Return (m, t1, t2) with exact witnesses, trying every signed divisor m of 2730."""
    divs = [d for d in range(1, 2731) if 2730 % d == 0]
    for m in divs + [-d for d in divs]:
        A = m * B
        if A == B * B:
            continue
        beta = core(A)
        theta = core(m * (m - B))
        classes = {}
        for t in small_t(bound):
            n = n_of_t(beta, t)
            if n == 0:
                continue
            classes.setdefault(core(n), t)
        for c1, t1 in classes.items():
            c2 = core(theta * c1)
            if c2 in classes:
                t2 = classes[c2]
                wit = witnesses(B, m, t1, t2)
                if wit is not None:
                    assert pole_poly(B, *wit) == 0
                    return m, t1, t2
    return None


def random_admissible_B(rng):
    """B with square reduced denominator, 0 < B < 1/2, v_p(B) >= 4 on S0."""
    K = 2**4 * 3**6 * 5**6 * 7**6 * 13**6
    while True:
        u = rng.randrange(1, 10**4)
        lo = isqrt(2 * K * u) + 1
        v = rng.randrange(lo, 4 * lo)
        B = F(K * u, v * v)
        if 0 < B < F(1, 2) and all(F(B).numerator % p**k == 0 for p, k in [(2, 4), (3, 4), (5, 4), (7, 4), (13, 4)]):
            return B


if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    bound = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    rng = random.Random(seed)
    found = 0
    for i in range(N):
        B = random_admissible_B(rng)
        res = search(B, bound)
        print(i, "B =", B, "->", res, flush=True)
        found += res is not None
    print(f"solutions with exact witnesses: {found}/{N} (height bound {bound})")
