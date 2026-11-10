"""Constant slopes.  T0 = rationals t = u/v (|u|, v <= H) satisfying GoodSlope 0 with no odd
contact prime above 324 (S_b = S_ht, i.e. catalogue removed).  Then: for which integers A is
A - k1 - k2 (k1, k2 in T0) itself a good slope?  If two constant slopes worked for all A, one
variable slope would suffice; the test measures how fast this fails."""
import cypari2, math, sys
from fractions import Fraction
pari = cypari2.Pari()
C = [0, -15, -20, -24, -30, -60]
H = int(sys.argv[1]) if len(sys.argv) > 1 else 200
AMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
cache = {}
def fac(n):
    n = abs(n)
    if n not in cache:
        cache[n] = {int(p): int(e) for p, e in zip(*pari.factor(n))} if n > 1 else {}
    return cache[n]
goodp = {}
def good_prime(p):
    if p not in goodp:
        if p % 8 != 1 or pari.kronecker(7, p) != -1: goodp[p] = False
        else:
            a, b = [int(x) for x in pari.qfbsolve(pari.Qfb(1, 0, 1), p)]
            if a % 2 == 0: a, b = b, a
            g = math.gcd(a, p + 1)
            while g % 2 == 0: g //= 2
            goodp[p] = g == 1
    return goodp[p]
def check(u, v):
    """None if t = u/v is not a good slope, else the number of odd contact primes > 324."""
    if v == 0 or u == v or any(u == c*v for c in C): return None
    nums = [u - c*v for c in C]
    val = {}
    for x in nums:
        for p, e in fac(x).items(): val[p] = val.get(p, 0) + e
    vv, w = fac(v), fac(u - v)
    big = 0
    for p, e in val.items():
        if p <= 324: continue
        if e % 2:
            # odd contact prime: one contact, exponent 1, good
            if e != 1 or not good_prime(p): return None
            big += 1
    if big > 6: return None
    for q in pari.primes(324):
        q = int(q)
        vt1 = w.get(q, 0) - vv.get(q, 0)
        vF = val.get(q, 0) - 6*vv.get(q, 0) - 8*vt1
        if abs(vt1) > 4 or abs(vF) > 32: return None
    return big
T0 = []
for v in range(1, H + 1):
    for u in range(-H, H + 1):
        if math.gcd(u, v) == 1 and check(u, v) == 0: T0.append(Fraction(u, v))
print(f"H={H}: |T0| = {len(T0)}; integers in T0: {sorted(int(t) for t in T0 if t.denominator == 1)}")
print("denominators:", sorted(set(t.denominator for t in T0))[:40])
K = sorted(set(a + b for a in T0 for b in T0))
print(f"|T0 + T0| = {len(K)}")
hits = {}
for A in range(-AMAX, AMAX + 1):
    for k in K:
        t = Fraction(A) - k
        if check(t.numerator, t.denominator) is not None:
            hits[A] = k; break
for lo, hi in [(0, 100), (100, 300), (300, 1000), (1000, 3000), (3000, AMAX)]:
    if hi > AMAX or lo >= hi: continue
    n = sum(1 for A in range(lo, hi) if A in hits) + sum(1 for A in range(-hi + 1, -lo + 1) if A in hits)
    print(f"|A| in [{lo},{hi}): {n} of {2*(hi-lo)} integers are k1+k2+t with k1,k2 in T0, t good")
