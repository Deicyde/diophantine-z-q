"""t28-igusa: the special locus det(yv f) = 0. Checks: (1) even sextics x^6+a x^4+b x^2+1 (extra
involution x -> -x) have det(yv) = 0 identically; (2) det(Gram) = 4*det(yv)^2 is a polynomial in
J2..J10 (interpolation + fresh check), so the locus is defined by the Igusa invariants.
Run from the repo root: ~/pyenv/bin/python -I scratch/t28-igusa/special_check.py"""
import random, sympy as sp
x, z, p, q = sp.symbols('x z p q')
random.seed(7)
def tv(phi, psi, k):
    m = sp.Poly(phi, x, z).total_degree(); n = sp.Poly(psi, x, z).total_degree()
    s = sum((-1)**j * sp.binomial(k, j) * sp.diff(phi, x, k - j, z, j) * sp.diff(psi, x, j, z, k - j) for j in range(k + 1))
    return sp.expand(sp.factorial(m - k) * sp.factorial(n - k) / (sp.factorial(m) * sp.factorial(n)) * s)
def ys(c):
    f = sp.expand(sum(ci * x**i * z**(6 - i) for i, ci in enumerate(c)))
    i4 = tv(f, f, 4); y1 = tv(f, i4, 4); y2 = tv(i4, y1, 2); y3 = tv(i4, y2, 2)
    return sp.Matrix([[sp.expand(y).coeff(x, k).coeff(z, 2 - k) for k in range(3)] for y in (y1, y2, y3)])
print("(1) det yv(x^6 + p x^4 + q x^2 + 1) =", sp.factor(ys([1, 0, q, 0, p, 0, 1]).det()))
print("    det yv(x^5 + p x^3 + q x) =", sp.factor(ys([0, q, 0, p, 0, 1, 0]).det()))
