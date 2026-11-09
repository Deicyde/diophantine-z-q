"""Illustration for the five-contact set C5 = {-1, 0, 1, 2, 3}: rationals u = a/b (b > 0, lowest
terms) with M_S(u) = 1 for S = primes <= 13, i.e. every a - c b (c in C5) is +-(S-unit) * square.
Negative valuations of u are ignored, as in M_S.  Compares the sets found for two search bounds.
Also runs the same search for the 11/5 contact set for comparison.
"""
import sys
from math import gcd, isqrt, log

S = [2, 3, 5, 7, 11, 13]

def s_square_class_trivial(n):
    n = abs(n)
    if n == 0:
        return False
    for p in S:
        while n % p == 0:
            n //= p
    r = isqrt(n)
    return r * r == n

def search(C, bound):
    found = []
    for b in range(1, bound + 1):
        for a in range(-bound, bound + 1):
            if gcd(a, b) != 1:
                continue
            ok = True
            for c in C:
                if not s_square_class_trivial(a - c * b):
                    ok = False
                    break
            if ok:
                found.append((a, b))
    return found

for name, C in [("C5", [-1, 0, 1, 2, 3]), ("C6 (11/5)", [0, -15, -20, -24, -30, -60])]:
    res = {}
    for bound in (1200, 4000):
        f = search(C, bound)
        res[bound] = set(f)
        hmax = max(log(max(abs(a), b)) for a, b in f)
        arg = max(f, key=lambda ab: max(abs(ab[0]), ab[1]))
        print("%s, |a|,b <= %d: %d points, max height %.2f at %s/%s" % (name, bound, len(f), hmax, arg[0], arg[1]))
    new = sorted(res[4000] - res[1200], key=lambda ab: max(abs(ab[0]), ab[1]))
    print("   points found only with the larger bound:", new[:10])
