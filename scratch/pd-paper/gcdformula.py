"""Check F: for primes p = 1 (8), (p/7) = -1, p < PMAX, with any root r of r^2 = 2:
gcd(pointCount(-(75-53r)^2), pointCount(-(75+53r)^2)) = 4 gcd(c_p, p+1), c_p = phi_p(1)/2,
and {pointCounts} = {p+1-2c_p, p+1+2c_p}; also d*dbar = 7."""
import math, sys
PMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 6000
def isprime(n): return n > 1 and all(n % q for q in range(2, math.isqrt(n) + 1))
n = bad = 0
for p in range(3, PMAX):
    if not isprime(p) or p % 8 != 1 or pow(p % 7, 3, 7) != 6: continue
    chi = [0] + [1 if pow(x, (p-1)//2, p) == 1 else -1 for x in range(1, p)]
    phi = lambda a: sum(chi[(x**3 + a*x) % p] for x in range(p))
    c = phi(1) // 2
    for r in range(p):
        if (r*r - 2) % p: continue
        d, db = (75 - 53*r) % p, (75 + 53*r) % p
        assert d * db % p == 7 % p
        n1, n2 = p + 1 + phi((-d*d) % p), p + 1 + phi((-db*db) % p)
        n += 1
        if sorted([n1, n2]) != sorted([p+1-2*c, p+1+2*c]) or math.gcd(n1, n2) != 4 * math.gcd(c, p+1):
            bad += 1; print("fail", p, r)
print(f"check F: {n} (p, r) pairs, {bad} failures")
