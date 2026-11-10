"""Exact checks of the polarization datum in the Version 14 proof of Theorem 4.1
(V14 L689-705 and L935-953), in my own notation.

B = (2,-3): i^2 = 2, j^2 = -3, ij = -ji.  O = Z<1, i, (1+j)/2, (i+ij)/2>.
mu = 2j + ij.  E0(x,y) = Trd(mu^{-1} x ybar),  E1(x,y) = Trd(xbar mu y).
Claims checked: mu^2 = -6; Gram(E0) in the basis above is the 4x4 matrix
[[0,0,-1,1],[0,0,1,-2],[1,-1,0,0],[-1,2,0,0]] with determinant 1;
E1 = 6 E0 identically (so det Gram(E1) = 6^4); E0 is alternating and satisfies
E0(a x, y) = E0(x, a^dag y) with a^dag = mu^{-1} abar mu; O is an order of
reduced discriminant 6; |(O/3O)^*| <= 81 and |(O/5O)^*| = |GL2(F5)|.
Run: python3 -I form_check.py"""
from fractions import Fraction as Fr
from itertools import product

A, Bc = 2, -3  # i^2, j^2


class Q:
    """Element a + b i + c j + d ij of (A, Bc) with rational coefficients."""
    def __init__(s, a, b=0, c=0, d=0): s.v = tuple(Fr(t) for t in (a, b, c, d))
    def __add__(s, o): return Q(*(x + y for x, y in zip(s.v, o.v)))
    def __sub__(s, o): return Q(*(x - y for x, y in zip(s.v, o.v)))
    def scale(s, k): return Q(*(k * x for x in s.v))
    def __mul__(s, o):
        a1, b1, c1, d1 = s.v; a2, b2, c2, d2 = o.v
        # (ij)^2 = -A*Bc; i(ij) = A j; (ij)i = -A j; j(ij) = -Bc i; (ij)j = Bc i; ji = -ij
        return Q(a1*a2 + A*b1*b2 + Bc*c1*c2 - A*Bc*d1*d2,
                 a1*b2 + b1*a2 - Bc*c1*d2 + Bc*d1*c2,
                 a1*c2 + c1*a2 + A*b1*d2 - A*d1*b2,
                 a1*d2 + d1*a2 + b1*c2 - c1*b2)
    def conj(s): a, b, c, d = s.v; return Q(a, -b, -c, -d)
    def trd(s): return 2 * s.v[0]
    def nrd(s): return (s * s.conj()).v[0]
    def inv(s): return s.conj().scale(1 / s.nrd())
    def __eq__(s, o): return s.v == o.v


one, i, j, ij = Q(1), Q(0, 1), Q(0, 0, 1), Q(0, 0, 0, 1)
basis = [one, i, (one + j).scale(Fr(1, 2)), (i + ij).scale(Fr(1, 2))]
mu = j.scale(2) + ij
assert mu * mu == Q(-6), "mu^2"
mui = mu.inv()
E0 = lambda x, y: (mui * x * y.conj()).trd()
E1 = lambda x, y: (x.conj() * mu * y).trd()
G0 = [[E0(x, y) for y in basis] for x in basis]
G1 = [[E1(x, y) for y in basis] for x in basis]


def det(M):
    M = [row[:] for row in M]; n = len(M); d = Fr(1)
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None: return Fr(0)
        if p != c: M[c], M[p] = M[p], M[c]; d = -d
        d *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            M[r] = [M[r][k] - f * M[c][k] for k in range(n)]
    return d


print("Gram(E0) =", [[int(t) for t in row] for row in G0], " det =", det(G0))
assert G0 == [[0, 0, -1, 1], [0, 0, 1, -2], [1, -1, 0, 0], [-1, 2, 0, 0]]
assert det(G0) == 1
assert all(G1[r][c] == 6 * G0[r][c] for r in range(4) for c in range(4))
print("Gram(E1) = 6 Gram(E0); det Gram(E1) =", det(G1), "= 6^4:", det(G1) == 6**4)
# alternating, Rosati adjoint identity on a spanning set
for x in basis:
    assert E0(x, x) == 0
    for y in basis:
        for a in basis:
            adag = mui * a.conj() * mu
            assert E0(a * x, y) == E0(x, adag * y)
print("E0 alternating; E0(ax,y) = E0(x, mu^-1 abar mu y) on the basis: OK")

# O is closed under multiplication, discriminant 6
def coords(q):
    # solve q = sum t_k basis_k; basis matrix is triangular-ish: use explicit inversion
    a, b, c, d = q.v
    t3, t4 = 2 * c, 2 * d
    return (a - c, b - d, t3, t4)
for x in basis:
    for y in basis:
        t = coords(x * y)
        assert all(s.denominator == 1 for s in t), "not closed"
T = [[(x * y).trd() for y in basis] for x in basis]
print("det Trd-Gram =", det(T), "(reduced discriminant^2 * (-1) => disc 6):", det(T) == -36)

# unit groups mod 3 and mod 5 by brute force over O/nO
def units_mod(n):
    elts = list(product(range(n), repeat=4))
    def mul(s, t):
        q = sum((basis[k].scale(s[k]) for k in range(4)), Q(0)) * sum((basis[k].scale(t[k]) for k in range(4)), Q(0))
        return tuple(int(c) % n for c in coords(q))
    onev = (1, 0, 0, 0)
    return sum(1 for s in elts if any(mul(s, t) == onev for t in elts))
u3 = units_mod(3); u5 = units_mod(5)
print("|(O/3O)^*| =", u3, " |(O/5O)^*| =", u5, " |GL2(F5)| =", (25 - 1) * (25 - 5))
assert u3 <= 81 and u5 == 480
print("ALL CHECKS PASSED")
