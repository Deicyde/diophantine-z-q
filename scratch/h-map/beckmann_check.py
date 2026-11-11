"""Exact checks for the Beckmann-specialization route (h-map step 7).
Run: ~/pyenv/bin/python -I scratch/h-map/beckmann_check.py"""
from sympy import symbols, expand, resultant, discriminant, factorint, Rational, cancel, degree, Poly, factor
u = symbols('u')
F = u*(u+15)*(u+20)*(u+24)*(u+30)*(u+60)
G = 7*u**2 + 300*u + 3600
H = (u**2-60*u-1800)*(13*u**2+480*u+3600)*(11*u**2+600*u+7200)
print("G^6-97200F^2 == H^2:", expand(G**6-97200*F**2-H**2) == 0)
J = -57600*F**2/G**6
print("J + 16/27 == 16 H^2/(27 G^6):", cancel(J + Rational(16,27) - 16*H**2/(27*G**6)) == 0)
Jinf = Rational(-57600, 7**6)
print("J(oo) =", Jinf, " J(oo)+16/27 =", Jinf+Rational(16,27), factorint((Jinf+Rational(16,27)).p), factorint((Jinf+Rational(16,27)).q))
def primes_of(n): return sorted(factorint(abs(n)).keys())
print("Res(F,G) primes:", primes_of(resultant(F,G,u)))
print("Res(F,H) primes:", primes_of(resultant(F,H,u)))
print("Res(G,H) primes:", primes_of(resultant(G,H,u)))
print("disc(F) primes:", primes_of(discriminant(F,u)))
print("disc(G) primes:", primes_of(discriminant(G,u)))
print("disc(H) primes:", primes_of(discriminant(H,u)))
print("leading coeffs F,G,H:", Poly(F,u).LC(), Poly(G,u).LC(), primes_of(Poly(H,u).LC()))
# contact differences: primes p for which two contacts can both have positive valuation
C = [0,-15,-20,-24,-30,-60]
diffs = set()
for a in C:
    for b in C:
        if a != b: diffs |= set(primes_of(a-b))
print("primes dividing contact differences:", sorted(diffs))
print("57600 =", factorint(57600))
