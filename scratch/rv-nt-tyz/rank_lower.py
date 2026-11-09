"""Exact rank >= 3 for C_n : y^2 = x^3 - n^2 x, n in {26565, 33117}.

PARI's ellrank is used only to *find* points. Verification is exact and in pure Python:
points lie on the curve, and the Kummer images x -> (x, x - n) in (Q*/Q*^2)^2 of the two
2-torsion generators and the three points span an F_2-space of dimension 5. The Kummer map
E(Q)/2E(Q) -> (Q*/Q*^2)^2 is injective and dim E(Q)/2E(Q) = rank + 2, so rank >= 3.
As a second, numerical check, the regulator (determinant of the height pairing) is printed.
"""
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction
import sympy
import cypari2
from genus import rank_f2

pari = cypari2.Pari()
pari.allocatemem(2 * 10**9)


def sqfree_vector(q, basis):
    """Squarefree class of nonzero rational q as an F_2 vector over 'basis' (sign = -1 first)."""
    q = Fraction(q)
    num, den = q.numerator * q.denominator, 1  # same square class as num/den
    v = {-1: 1 if num < 0 else 0}
    for p, e in sympy.factorint(abs(num)).items():
        if e % 2:
            v[p] = 1
    for p in v:
        if p not in basis:
            basis.append(p)
    return v


def kummer(P, n):
    """(x, x - n) up to squares, with the usual fix at 2-torsion points."""
    x, y = P
    if y == 0:
        e = [Fraction(0), Fraction(n), Fraction(-n)]
        if x == 0:
            return ((-n) * n, -n)       # (e1-e2)(e1-e3), e1-e2
        if x == n:
            return (n, (n - 0) * (n + n))  # x - e1, (e2-e1)(e2-e3)
        if x == -n:
            return (-n, -2 * n)
    return (x, x - n)


def check(n, pts):
    for (x, y) in pts:
        assert y * y == x**3 - n * n * x, (x, y)
    gens = [(Fraction(0), 0), (Fraction(n), 0)] + pts
    basis = [-1]
    vecs = []
    for P in gens:
        a, b = kummer(P, n)
        vecs.append((sqfree_vector(a, basis), sqfree_vector(b, basis)))
    rows = [[va.get(p, 0) for p in basis] + [vb.get(p, 0) for p in basis] for va, vb in vecs]
    return rank_f2(rows)


def find_points(n):
    E = pari.ellinit([0, 0, 0, -n * n, 0])
    r = pari.ellrank(E)
    lo, hi, pts = int(r[0]), int(r[1]), r[3]
    out = []
    for P in pts:
        x, y = Fraction(str(P[0])), Fraction(str(P[1]))
        out.append((x, y))
    reg = pari.ellheightmatrix(E, pts).matdet() if len(pts) else 0
    return lo, hi, out, reg, E


if __name__ == "__main__":
    for n in (26565, 33117):
        lo, hi, pts, reg, E = find_points(n)
        print(f"n = {n}: ellrank bounds {lo}..{hi}; points {[(str(x), str(y)) for x, y in pts]}")
        dim = check(n, pts)
        print(f"  exact: all points on C_n; Kummer span of T1, T2 and {len(pts)} points has dim {dim}"
              f" => rank >= {dim - 2}")
        print(f"  height-pairing determinant (numerical) = {float(reg):.4f}")
        print(f"  root number = {pari.ellrootno(E)}, analytic rank (numerical) = {pari.ellanalyticrank(E)[0]}")
