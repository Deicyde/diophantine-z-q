"""Shared helpers for the descent-alt experiments (imports the exact 2-Selmer code of rv-route-k)."""
import os, sys, random
from fractions import Fraction as Fr
from math import gcd, isqrt
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "rv-route-k"))
import cypari2
pari = cypari2.Pari()
pari.allocatemem(2 * 10 ** 9)
from sel2cong import selmer, vec_of, first_coord_contains, F2Span  # noqa: E402

S0 = [2, 3, 5, 7, 13]
POS = [1, 2, 3, 5, 6, 7, 10, 13, 14, 15, 21, 26, 30, 35, 39, 42, 65, 70, 78, 91, 105, 130, 182,
       195, 210, 273, 390, 455, 546, 910, 1365, 2730]
DIVS = sorted({s * a for a in POS for s in (1, -1)}, key=lambda m: (m < 0, abs(m)))
_fc = {}


def factor(n):
    n = abs(int(n))
    if n not in _fc:
        _fc[n] = {int(p): int(e) for p, e in zip(*pari.factor(n))} if n > 1 else {}
    return _fc[n]


def sqf_int(n):
    out = -1 if n < 0 else 1
    for p, e in factor(n).items():
        if e % 2:
            out *= p
    return out


def sqfQ(r):
    r = Fr(r)
    return sqf_int(r.numerator * r.denominator)


def vpQ(r, p):
    r = Fr(r)
    def v(n):
        n = abs(n); k = 0
        while n % p == 0:
            n //= p; k += 1
        return k
    return v(r.numerator) - v(r.denominator)


def admissible(B):
    B = Fr(B)
    d = B.denominator
    return isqrt(d) ** 2 == d and 0 < B < Fr(1, 2) and all(vpQ(B, p) >= 4 for p in S0)


def oddprimes(d):
    return sorted(p for p in factor(d) if p != 2)


def sel(d):
    return selmer(d, oddprimes(d))


def good(d, beta):
    """'torsion' if beta = +-d mod squares; 'selmer3' if dim Sel2(C_d) = 3 and beta is a first
    coordinate; else None."""
    if sqf_int(beta * d) in (1, -1):
        return "torsion"
    basis, gens = sel(d)
    if len(basis) == 3 and first_coord_contains(basis, vec_of(beta, gens)):
        return "selmer3"
    return None


def info(d, beta):
    """(dim Sel2, beta in first-coordinate projection)."""
    basis, gens = sel(d)
    return len(basis), first_coord_contains(basis, vec_of(beta, gens))


def beta_theta(B, m):
    return sqfQ(m * B), sqfQ(m * (m - B))


def gen_random(rng, ulim=10 ** 7):
    while True:
        base = 1
        for p in S0:
            base *= p ** rng.randint(4, 7)
        u = rng.randrange(1, ulim)
        if gcd(u, 2730) != 1:
            continue
        N = base * u
        lo = isqrt(2 * N) + 1
        while True:
            D = rng.randrange(lo, 50 * lo)
            if gcd(D, N) == 1:
                break
        B = Fr(N, D * D)
        if admissible(B):
            return B


def gen_with_beta_primes(rng, plist, dmult=3):
    """N = S0-part * product of the given primes (odd exponent)."""
    while True:
        base = 1
        for p in S0:
            base *= p ** rng.randint(4, 7)
        u = 1
        for p in plist:
            u *= p
        N = base * u
        lo = isqrt(2 * N) + 1
        while True:
            D = rng.randrange(lo, dmult * lo)
            if gcd(D, N) == 1:
                break
        B = Fr(N, D * D)
        if admissible(B):
            return B
