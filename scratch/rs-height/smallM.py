"""Rationals t = a/b (|a| <= N, 1 <= b <= N) with M_S(t) = 1 for S = primes <= 13, i.e. every
t - c (c in the contact set) is a square times an S-unit: rational points on the finitely many
twists of the genus-17 fibre product of conics.  Prints the points and their heights."""
from math import gcd, isqrt, log
import sys
N = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
S = [2, 3, 5, 7, 11, 13]
C = [0, -15, -20, -24, -30, -60]
def sq_times_unit(x):
    x = abs(x)
    for p in S:
        while x % p == 0:
            x //= p
    r = isqrt(x)
    return r * r == x
pts = []
for b in range(1, N + 1):
    for a in range(-N, N + 1):
        if gcd(a, b) != 1:
            continue
        if any(a == c * b for c in C):
            continue
        if all(sq_times_unit(a - c * b) for c in C):
            pts.append((a, b))
pts.sort(key=lambda ab: max(abs(ab[0]), ab[1]))
print(len(pts), "points with M_S = 1, S = primes <= 13, |a|,b <=", N)
print("largest heights:", [(a, b, round(log(max(abs(a), b)), 2)) for a, b in pts[-12:]])
