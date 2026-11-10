"""Exact checks of the Version 14 normalization chain for the discriminant-six
Shimura curve (V14 proof of Theorem 4.1, L725-753 and L1605-1634), and of the
coordinate identity used by the NoCM lemma (h-cm, rv-h-cm).

Inputs are restated from the sources in my own notation, not copied:
  * Lin-Yang (arXiv:1807.00466v1, Example on X_6): along the curve,
    s3^2/s2^3 = c1 j, s5/(s2 s3) = c2, s6/s2^3 = c3 j + c4, and on the
    curve Y'_5 the parametrization
    [s2,s3,s5,s6] = [(x-12)^2, x(x^2-36x-432), -2^10 3^5 x, 2^10 3^5 (x^2+12x+12)],
    with x = -6 +- 6 sqrt(-3) at the CM point of discriminant -24, and on Y_1
    [s2,s3,s5,s6] = [J^2, J^2 (J-1728), 0, 2^12 3^6 J^4] (J = elliptic j).
  * Lin-Yang relations: J2 = -3 chi12/chi10, J4 = (J2^2 - psi4)/24,
    J6 = (-J2^3 + 36 J2 J4 + psi6)/216, J10 = -4 chi10, and
    s2 = psi4, s3 = psi6, s5 = 2^12 3^5 chi10, s6 = 2^12 3^6 chi12.
  * Igusa's theta normalization (UNCHECKED primary source, as cited by V14):
    psi4 = 2^-2 sum z^8, chi10 = -2^-14 prod z^2 (ten even characteristics).
Run: /path/to/python -I igusa_check.py  (needs sympy)."""
from sympy import symbols, sqrt, I, Rational, simplify, expand, factor, Poly

j, x, u = symbols('j x u')

# 1. Constants c1..c4 from the discriminant -24 point on Y'_5 and the -4 point on Y_1.
xv = -6 + 6*sqrt(3)*I
assert simplify(xv**2 + 12*xv + 144) == 0
s2 = (xv - 12)**2
s3 = xv*(xv**2 - 36*xv - 432)
s5 = -2**10 * 3**5 * xv
s6 = 2**10 * 3**5 * (xv**2 + 12*xv + 12)
vals = [simplify(expand(e)) for e in (s2 + 36*xv, s3, s5 + 248832*xv, s6)]
print("s2+36x, s3, s5+248832x, s6 at x=-6+6sqrt(-3):", vals)
r1 = simplify(s3**2 / s2**3); r2 = simplify(s5 / (s2*s3)); r3 = simplify(s6 / s2**3)
print("ratios at disc -24:", r1, r2, r3)
assert (r1, r2, r3) == (Rational(-16, 27), 1, Rational(11, 27))
c4 = Rational(2**12 * 3**6, 1728**2)   # Y_1 at J = 1728 (disc -4): s6/s2^3 = 2^12 3^6 J^4 / J^6
assert c4 == 1
jm24 = Rational(-16, 27)
c1 = r1 / jm24; c2 = r2; c3 = (r3 - c4) / jm24
print("c1..c4 =", c1, c2, c3, c4)
assert (c1, c2, c3) == (1, 1, 1)
# cross-check against Lin-Yang's own determination at discriminant -19 (j = 81/64)
assert c1 * Rational(81, 64) == Rational(81, 64) and c3 * Rational(81, 64) + c4 == Rational(145, 64)

# 2. With c1=c2=c3=c4=1, [s2,s3,s5,s6] = [j, j^2, j^3, j^3 (j+1)] solves the relations.
S2, S3, S5, S6 = j, j**2, j**3, j**3*(j + 1)
assert simplify(S3**2/S2**3 - j) == 0 and simplify(S5/(S2*S3) - 1) == 0 and simplify(S6/S2**3 - (j + 1)) == 0
psi4, psi6 = S2, S3
chi10 = S5 / (2**12 * 3**5); chi12 = S6 / (2**12 * 3**6)
J2 = simplify(-3*chi12/chi10)
J4 = simplify((J2**2 - psi4)/24)
J6 = simplify((-J2**3 + 36*J2*J4 + psi6)/216)
J10 = simplify(-4*chi10)
lam = -12  # weighted rescaling, weights 1,2,3,5
vec = [factor(expand(lam**w * e)) for w, e in ((1, J2), (2, J4), (3, J6), (5, J10))]
print("[J2,J4,J6,J10] after rescaling by -12:", vec)
target = [12*(j + 1), 6*(j**2 + j + 1), 4*(j**3 - 2*j**2 + 1), j**3]
assert all(simplify(a - b) == 0 for a, b in zip(vec, target))

# 3. psi4, chi10 in the rescaled representative, and the theta formula constant.
J2r, J4r, J10r = target[0], target[1], target[3]
psi4r = expand(J2r**2 - 24*J4r); chi10r = -J10r/4
print("psi4 =", psi4r, " chi10 =", chi10r)
assert psi4r == 144*j and simplify(chi10r + j**3/4) == 0
assert simplify(16 * 144**5 * chi10r**2 / psi4r**5 - j) == 0
# Igusa: psi4 = 2^-2 Sigma, chi10 = -2^-14 Pi  =>  chi10^2/psi4^5 = 2^-28 Pi^2 / (2^-10 Sigma^5)
const = Rational(16 * 144**5, 2**18)
print("16*144^5*2^-28/2^-10 =", const)
assert const == 3779136

# 4. The NoCM coordinate identity (h-cm): t = 1 + 27 J(u)/16 = H^2/G^6.
F = u*(u + 15)*(u + 20)*(u + 24)*(u + 30)*(u + 60)
G = 7*u**2 + 300*u + 3600
H = (u**2 - 60*u - 1800)*(13*u**2 + 480*u + 3600)*(11*u**2 + 600*u + 7200)
assert expand(G**6 - 97200*F**2 - H**2) == 0
Ju = -57600*F**2/G**6
assert simplify(1 + Rational(27, 16)*Ju - H**2/G**6) == 0
assert Rational(27 * 57600, 16) == 97200
# Moebius map j -> t = 1 + 27 j/16 sends (0, oo, -16/27) to (1, oo, 0): Elkies' t at discs -4, -3, -24.
assert 1 + Rational(27, 16)*0 == 1 and 1 + Rational(27, 16)*Rational(-16, 27) == 0
print("NoCM identity G^6 - 97200 F^2 = H^2 and t(u) = H^2/G^6: OK")
print("ALL CHECKS PASSED")
