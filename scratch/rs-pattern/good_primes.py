"""C1. Check the CM description of GoodPatternPrime against brute-force point counts,
and measure the density of good primes (and of the order-based relaxation).

GoodPatternPrime p (PrimePattern.lean): p prime, p != 2, exists r with r^2 = 2,
75 -+ 53 r != 0, gcd(N1, N2) = 4 and p does not divide N1 N2, where
Ni = #E_i(F_p) for E_1: y^2 = x^3 - (75 - 53 r)^2 x, E_2: y^2 = x^3 - (75 + 53 r)^2 x.
"""
import sys
import numpy as np
from math import gcd
from ntlib import primes_upto, legendre, sqrt_mod, good_cm, two_squares, odd_part

def count(p, a):
    """#{(x, y) in F_p^2 : y^2 = x^3 + a x} + 1."""
    y = np.arange(p, dtype=np.int64)
    cnt = np.bincount(y * y % p, minlength=p)
    x = np.arange(p, dtype=np.int64)
    f = (x * x % p * x + a * x) % p
    return int(cnt[f].sum()) + 1

def factor(n):
    f, d = {}, 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1; n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

def ec_add(P, Q, a, p):
    if P is None: return Q
    if Q is None: return P
    x1, y1 = P; x2, y2 = Q
    if x1 == x2 and (y1 + y2) % p == 0:
        return None
    if P == Q:
        lam = (3 * x1 * x1 + a) * pow(2 * y1, -1, p) % p
    else:
        lam = (y2 - y1) * pow(x2 - x1, -1, p) % p
    x3 = (lam * lam - x1 - x2) % p
    return (x3, (lam * (x1 - x3) - y1) % p)

def ec_mul(n, P, a, p):
    R = None
    while n:
        if n & 1: R = ec_add(R, P, a, p)
        P = ec_add(P, P, a, p); n >>= 1
    return R

def order(P, N, a, p):
    """Order of P in a group of order N (N annihilates P)."""
    e = N
    for q, k in factor(N).items():
        for _ in range(k):
            if ec_mul(e // q, P, a, p) is None:
                e //= q
            else:
                break
    return e

def P0_at(r, p):
    i8, i32 = pow(8, -1, p), pow(32, -1, p)
    return ((1641 - 1160 * r) * i8 % p, (-123720 + 87483 * r) * i32 % p)

def main(bound):
    n_all = n_split = n_good = n_pred = 0
    mismatch = []
    n_cls = 0          # p = 1 mod 8 and (p/7) = -1
    n_order_good = 0   # same class, gcd(e1, e2) | 4 (orders of P0)
    for p in primes_upto(bound):
        p = int(p)
        if p <= 7:
            continue
        n_all += 1
        if p % 8 not in (1, 7):
            if good_cm(p):
                mismatch.append(p)
            continue
        n_split += 1
        r = sqrt_mod(2, p)
        d1, d2 = (75 - 53 * r) % p, (75 + 53 * r) % p
        if d1 == 0 or d2 == 0:
            lean_good = False
        else:
            N1 = count(p, (-d1 * d1) % p); N2 = count(p, (-d2 * d2) % p)
            lean_good = gcd(N1, N2) == 4 and (N1 * N2) % p != 0
        pred = good_cm(p)
        n_good += lean_good; n_pred += pred
        if lean_good != pred:
            mismatch.append(p)
        if p % 8 == 1 and legendre(p, 7) == -1 and d1 and d2:
            n_cls += 1
            a1, a2 = (-d1 * d1) % p, (-d2 * d2) % p
            e1 = order(P0_at(r, p), N1, a1, p)
            e2 = order(P0_at(-r % p, p), N2, a2, p)
            n_order_good += (odd_part(gcd(e1, e2)) == 1 and gcd(e1, e2) % 8 != 0)
    print(f"primes 7 < p <= {bound}: {n_all}; split in Q(sqrt2): {n_split}")
    print(f"GoodPatternPrime (brute force): {n_good}; CM prediction: {n_pred}; mismatches: {mismatch[:10]}")
    print(f"relative density of good primes among all primes: {n_good / n_all:.4f}")
    print(f"class p = 1 mod 8, (p/7) = -1: {n_cls} ({n_cls / n_all:.4f}); of these good: {n_good / n_cls:.4f}")
    print(f"same class with gcd(e1, e2) | 4 for the orders of P0: {n_order_good / n_cls:.4f}")

if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 20000)
