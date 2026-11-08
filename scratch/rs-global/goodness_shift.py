"""How much of the good-prime condition can a larger fixed shift absorb?

For split p (p = +-1 mod 8) let d1, d2 be the orders of y^2 = x^3 - (75 -+ 53 r)^2 x over F_p,
r^2 = 2. The multiplication test with fixed shift c needs gcd(e1, e2) | c for the orders e_i of P0;
we use the group orders d_i (as GoodPatternPrime does), and the condition
  G_L: v_2(gcd(d1, d2)) <= 2 and every odd prime factor of gcd(d1, d2) is <= L,
which is gcd | c for c = 4 * prod_{3 <= l <= L} l^N with N large.
L = 1 is the manuscript's gcd = 4 (up to the extra condition p not dividing d1 d2).
"""
import numpy as np
from math import gcd

def primes_upto(n):
    s = np.ones(n + 1, bool); s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]

def count(p, a):
    x = np.arange(p, dtype=np.int64)
    f = (x * x % p * x + a * x) % p
    sq = np.zeros(p, bool); sq[(x * x) % p] = True
    chi = np.where(f == 0, 0, np.where(sq[f], 1, -1))
    return p + 1 + int(chi.sum())

def odd_part(n):
    while n % 2 == 0: n //= 2
    return n

def largest_prime_factor(n):
    best, q = 1, 2
    while q * q <= n:
        while n % q == 0: best, n = q, n // q
        q += 1
    return max(best, n) if n > 1 else best

LIM = 40000
Ls = [1, 3, 10, 30, 100, 324, 1000]
tot = 0; split = 0; cls = 0
good = {L: 0 for L in Ls}; good_cls = {L: 0 for L in Ls}
for p in primes_upto(LIM):
    p = int(p)
    if p < 11: continue
    tot += 1
    if p % 8 not in (1, 7): continue
    split += 1
    r = next(r for r in range(p) if r * r % p == 2)
    a1 = (-(75 - 53 * r) ** 2) % p; a2 = (-(75 + 53 * r) ** 2) % p
    if (75 - 53 * r) % p == 0 or (75 + 53 * r) % p == 0: continue
    d1, d2 = count(p, a1), count(p, a2)
    g = gcd(d1, d2)
    incls = (p % 8 == 1) and pow(7, (p - 1) // 2, p) == p - 1
    cls += incls
    two_ok = (g % 8 != 0)
    lp = largest_prime_factor(odd_part(g))
    for L in Ls:
        if two_ok and lp <= L:
            good[L] += 1; good_cls[L] += incls
print("primes 11..%d: %d; split in Q(sqrt2): %d; class p=1 (8), (7/p)=-1: %d" % (LIM, tot, split, cls))
for L in Ls:
    print("L = %4d: good %5d = %.3f of all primes; in-class %.3f of the class; outside class %d" %
          (L, good[L], good[L] / tot, good_cls[L] / cls, good[L] - good_cls[L]))
