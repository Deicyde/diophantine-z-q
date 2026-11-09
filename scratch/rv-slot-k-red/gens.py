"""Generators of admissible inputs B (own code).  Each returns a Fraction B (checked admissible)
and, when designed for a particular multiplier, that multiplier."""
from fractions import Fraction as Fr
import random
import gmpy2
from sympy import primerange, isprime
from construct import admissible, sqf_rat, DIVS, factor

SMALLP = list(primerange(17, 2000))


def rand_prime(rng, lo, hi, cls=None, mod=8):
    while True:
        p = rng.randrange(lo, hi)
        if cls is not None and p % mod != cls:
            continue
        if gmpy2.is_prime(p):
            return p


def gen_random(rng, kmax=6):
    """B = N / D^2 with v_p(N) in 4..7 on S0 and random extra primes."""
    while True:
        N = 2 ** rng.randint(4, 7) * 3 ** rng.randint(4, 7) * 5 ** rng.randint(4, 7) \
            * 7 ** rng.randint(4, 7) * 13 ** rng.randint(4, 7)
        for p in rng.sample(SMALLP, rng.randint(0, kmax)):
            N *= p
        D = rng.randrange(1, 10**4)
        while gmpy2.gcd(D, N) != 1 or D * D <= 2 * N:
            D = D * rng.randint(2, 9) + 1
        B = Fr(N, D * D)
        if admissible(B):
            return B


def B_from_beta_t(beta, m, t):
    """B with B/m = beta t^2 (then sqf(mB) = beta and theta = sqf(1 - beta t^2))."""
    return Fr(m) * beta * t * t


def gen_from_beta(rng, beta, m=None, abound=50, bbits=None, want=None, tries=4000):
    """Given signed squarefree odd beta, find m (mbeta > 0) and t = 2730^2 a/b with B admissible.
    want(theta, T) filters theta."""
    ms = [mm for mm in DIVS if mm * beta > 0] if m is None else [m]
    for _ in range(tries):
        mm = rng.choice(ms)
        a = rng.randint(1, abound)
        bmin = int(2730 ** 2 * a * (2 * abs(mm * beta)) ** 0.5) + 2
        b = rng.randrange(bmin, bmin * rng.choice([2, 10, 1000]))
        t = Fr(2730 ** 2 * a, b)
        B = B_from_beta_t(beta, mm, t)
        if not admissible(B):
            continue
        th, T = sqf_rat(mm * (mm - B))
        if want is None or want(th, T):
            return B, mm
    return None, None


def gen_theta_one(rng, beta, j=None):
    """theta = 1: B/m = beta t^2 with t = 2k/(beta + k^2) (point on beta t^2 + c^2 = 1)."""
    ms = [mm for mm in DIVS if mm * beta > 0]
    for _ in range(2000):
        k = Fr(2730 ** 2 * rng.randint(1, 10**3), rng.randint(1, 10**3))
        t = 2 * k / (beta + k * k)
        mm = rng.choice(ms)
        B = B_from_beta_t(beta, mm, t)
        if admissible(B):
            th, T = sqf_rat(mm * (mm - B))
            assert th == 1
            return B, mm
    return None, None
