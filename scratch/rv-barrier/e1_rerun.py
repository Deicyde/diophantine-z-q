"""Rerun of el-gadget E1 (independent code). 30 primes p (every other prime in [331, 1000)).
For each p and each genus-0 gadget, take B = c/p (c small, p-unit) so v_p(B) = -1, multiplier m in
divisors of 2730 (p-units), and search an exact rational witness with PARI qfsolve.
G1: x^2 + y^2 = m(m-B); prediction (Hilbert symbol): witness iff p = 1 mod 4 (for the local part at p).
G2: x^2 - m y^2 = m - B;  G3: (1/B)^2 - m x^2 - (m-B) y^2 + m(m-B) z^2 = 1;  G5: x^2 - R0 y^2 = m(m-B), B=R0 s^2.
Usage: ~/pyenv/bin/python -I e1_rerun.py"""
import cypari2, math
from fractions import Fraction as Fr
from sympy import primerange
pari = cypari2.Pari()
M = [d for d in range(1, 2731) if 2730 % d == 0][:16]
def v(p, x):
    x = Fr(x); n, d = x.numerator, x.denominator; k = 0
    if n == 0: return 10**9
    while n % p == 0: n //= p; k += 1
    while d % p == 0: d //= p; k -= 1
    return k
def zero_last_nonzero(cs):
    den = 1
    for c in cs: den = den * c.denominator // math.gcd(den, c.denominator)
    ci = [int(c * den) for c in cs]
    s = pari.qfsolve(pari.matdiagonal(ci))
    if str(pari.type(s)) != 't_COL': return None
    x = [Fr(int(pari.numerator(t)), int(pari.denominator(t))) for t in s]
    n = len(ci)
    if x[-1] != 0: return x
    for j in range(n):          # move off the hyperplane last = 0 along an isotropic line
        y = [Fr(0)] * n; y[j] = Fr(1)
        bxy = ci[j] * x[j]
        if bxy == 0: continue
        lam = -Fr(ci[j]) / (2 * bxy)
        z = [y[i] + lam * x[i] for i in range(n)]
        if z[-1] != 0: return z
    return None
def gad(name, B, m, R0=None):
    if name == "G1": return [Fr(1), Fr(1), -Fr(m) * (m - B)]
    if name == "G2": return [Fr(1), -Fr(m), -(m - B)]
    if name == "G3": return [-Fr(m), -(m - B), Fr(m) * (m - B), 1 / (B * B) - 1]
    if name == "G5": return [Fr(1), -Fr(R0), -Fr(m) * (m - B)]
primes = list(primerange(331, 1000))[::2][:30]
tot = {}
mismatch = 0
for name in ["G1", "G2", "G3", "G5"]:
    cnt = 0
    for p in primes:
        hit = None
        for c in range(1, 40):
            for m in M:
                if name == "G5":
                    R0 = Fr(c * p); B = R0 / Fr(p * p)        # B = R0 sigma^2, sigma = 1/p, v_p(B) = -1
                else:
                    R0 = None; B = Fr(c, p)
                cs = gad(name, B, m, R0)
                if any(t == 0 for t in cs): continue
                z = zero_last_nonzero(cs)
                if z and sum(a * t * t for a, t in zip(cs, z)) == 0:
                    assert v(p, B) == -1
                    hit = (c, m); break
            if hit: break
        cnt += bool(hit)
        if name == "G1" and bool(hit) != (p % 4 == 1): mismatch += 1
    tot[name] = cnt
    print(name, "witness at v_p(B) = -1 for", cnt, "of", len(primes), "primes")
print("G1 primes = 1 mod 4 among sample:", sum(p % 4 == 1 for p in primes), "; G1 mismatches with Hilbert prediction:", mismatch)
