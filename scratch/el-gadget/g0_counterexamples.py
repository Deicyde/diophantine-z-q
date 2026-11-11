"""E1: Theorem G in practice. For genus-0 gadgets whose coefficients depend on the input,
find rational inputs B with v_p(B) = -1 at a prime p > 324 together with EXPLICIT rational
witnesses (exact check).  Usage: ~/pyenv/bin/python g0_counterexamples.py"""
import cypari2
from fractions import Fraction as Fr
from sympy import primerange, factorint
pari = cypari2.Pari()
M = [d for d in range(1, 2731) if 2730 % d == 0]          # positive divisors of 2730

def v(p, x):
    x = Fr(x); n, d = x.numerator, x.denominator
    if n == 0: return 10**9
    k = 0
    while n % p == 0: n //= p; k += 1
    while d % p == 0: d //= p; k -= 1
    return k

def solve_form(coeffs):
    """Rational zero of diag(coeffs) (list of Fractions) with last coordinate != 0, or None."""
    den = 1
    for c in coeffs: den = den * c.denominator // __import__('math').gcd(den, c.denominator)
    ci = [int(c * den) for c in coeffs]
    G = pari.matdiagonal(ci)
    s = pari.qfsolve(G)
    if str(pari.type(s)) != 't_COL':
        return None
    x = [Fr(int(pari.numerator(t)), int(pari.denominator(t))) for t in s]
    if x[-1] == 0:
        # isotropic: Q = H + rest; use x and a vector y with B(x,y) != 0 to make last coord nonzero
        n = len(ci)
        for j in range(n):
            y = [Fr(0)] * n; y[j] = Fr(1)
            bxy = sum(Fr(ci[i]) * x[i] * y[i] for i in range(n))
            if bxy == 0: continue
            qy = sum(Fr(ci[i]) * y[i] ** 2 for i in range(n))
            lam = -qy / (2 * bxy)          # Q(y + lam x) = qy + 2 lam bxy = 0
            z = [y[i] + lam * x[i] for i in range(n)]
            if z[-1] != 0: return z
        return None
    return x

def check(coeffs, z):
    return sum(c * t * t for c, t in zip(coeffs, z)) == 0

# Gadgets: each returns list of diagonal coefficient lists (homogeneous, last coord = 1 after scaling);
# a rational zero with last coordinate != 0 is a witness for Phi'(input).
def G1(B, m):   # x^2 + y^2 = m(m-B)                (norm form of Q(i), input in the value)
    return [Fr(1), Fr(1), -Fr(m) * (m - B)]
def G2(B, m):   # x^2 - m y^2 = (m - B)              (coefficients from multiplier, value from input)
    return [Fr(1), -Fr(m), -(m - B)]
def G3(B, m):   # Poonen-type: 2/B in S_{m, m-B}:  (1/B)^2 - m x^2 - (m-B) y^2 + m(m-B) z^2 = 1
    return [-Fr(m), -(m - B), Fr(m) * (m - B), Fr(1, 1) * (1 / (B * B)) - 1]
def G5(B, m, R0):  # multi-input, B = R0*sigma^2: x^2 - R0 y^2 = m(m - B)
    return [Fr(1), -Fr(R0), -Fr(m) * (m - B)]

results = {}
primes = list(primerange(331, 700))
for name in ["G1", "G2", "G3", "G5"]:
    bad_found = 0; examples = []
    for p in primes:
        found = None
        for num in range(1, 60):                       # B = num/p * (small square adjustments)
            if num % p == 0: continue
            for sq in (1, 4, 9):
                B = Fr(num, p * sq)
                if not (0 < B < Fr(1, 2)) and name != "G3": pass
                for m in M[:16]:
                    if name == "G5":
                        R0 = Fr(num * p); sigma = Fr(1, p * (1 if sq == 1 else int(sq ** 0.5)))
                        Bv = R0 * sigma ** 2
                        cs = G5(Bv, m, R0); Bused = Bv
                    else:
                        cs = globals()[name](B, m); Bused = B
                    if any(c == 0 for c in cs): continue
                    z = solve_form(cs)
                    if z is not None and check(cs, z):
                        assert v(p, Bused) % 2 == 1 and v(p, Bused) < 0
                        found = (str(Bused), m, [str(t / z[-1]) for t in z[:-1]]); break
                if found: break
            if found: break
        if found:
            bad_found += 1
            if len(examples) < 3: examples.append((p, found))
    results[name] = (bad_found, len(primes), examples)
    print(name, "primes p in [331,700) with an explicit witness at v_p(B) = -1:",
          bad_found, "/", len(primes))
    for e in examples: print("   ", e)
