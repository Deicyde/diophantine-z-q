"""Where does the genus-2 CURVE model of the QM fibre degenerate?
Igusa invariants on X^6/W (manuscript line 538, Lin-Yang (2),(14)):
  [J2,J4,J6,J10] = [12(j+1), 6(j^2+j+1), 4(j^3-2j^2+1), j^3],  j = J(u) = -57600 F(u)^2 / G(u)^6.
Liu's criterion: potentially good reduction of the curve at p iff J_{2i}^5 / J_{10}^i is p-integral
for all i (i=1 suffices to show BAD reduction).  We test u = c + p^k w (k = 1, 2: odd and EVEN
contact valuation) and u near a root of G mod p, and report v_p(J2^5/J10)."""
from fractions import Fraction as Fr
from sympy import factorint, sqrt_mod
C = [0, -15, -20, -24, -30, -60]
def F(u):
    r = Fr(1)
    for c in C: r *= (u - c)
    return r
def G(u): return 7*u*u + 300*u + 3600
def vp(x, p):
    x = Fr(x)
    if x == 0: return None
    v = 0; n, d = x.numerator, x.denominator
    while n % p == 0: n //= p; v += 1
    while d % p == 0: d //= p; v -= 1
    return v
rows = []
for p in [331, 337, 347, 349, 353]:          # primes outside S_ht = primes <= 324
    for (c, k) in [(-15, 1), (-15, 2), (-24, 2)]:
        u = Fr(c) + Fr(p**k, 7)                # contact valuation k at c, 0 elsewhere
        j = -57600 * F(u)**2 / G(u)**6
        rows.append((p, f"u={c}+p^{k}/7", vp(u - c, p), vp(j, p), vp(Fr(12)**5*(j+1)**5/j**3, p)))
    r = sqrt_mod(-10800 * pow(4*49, 1, p) % p, p)   # roots of G mod p exist iff -10800 is a square mod p
    if r is not None:
        # root of 7u^2+300u+3600 mod p: u = (-300 +- sqrt(disc))/14
        u0 = ((-300 + sqrt_mod(-10800 % p, p)) * pow(14, -1, p)) % p
        # Hensel-lift to precision p^2 and take u = lift + p^2
        for _ in range(3):
            u0 = (u0 - G(u0) * pow(14*u0 + 300, -1, p**3)) % p**3
        u = Fr(u0 + p**2)
        j = -57600 * F(u)**2 / G(u)**6
        rows.append((p, "u near root of G", vp(G(u), p), vp(j, p), vp(Fr(12)**5*(j+1)**5/j**3, p)))
print("p, input, v_p(u-c) or v_p(G(u)), v_p(j), v_p(J2^5/J10)")
for r in rows: print(*r)
print("all J2^5/J10 non-integral:", all(r[4] < 0 for r in rows), " #inputs:", len(rows))
