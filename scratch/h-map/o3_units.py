"""Unit group of O/3O for O = Z<1, i, (1+j)/2, (i+ij)/2>, B = (2,-3): i^2=2, j^2=-3, ij=-ji.
Counts units and norm-one units mod 3 (h-map step 8). Run: ~/pyenv/bin/python -I scratch/h-map/o3_units.py"""
from fractions import Fraction as Fr
from itertools import product
# quaternion arithmetic in basis 1,i,j,k=ij with i^2=a, j^2=b, k^2=-ab
a, b = 2, -3
def mul(x, y):
    x0,x1,x2,x3 = x; y0,y1,y2,y3 = y
    return (x0*y0 + a*x1*y1 + b*x2*y2 - a*b*x3*y3,
            x0*y1 + x1*y0 - b*x2*y3 + b*x3*y2,
            x0*y2 + x2*y0 + a*x1*y3 - a*x3*y1,
            x0*y3 + x3*y0 + x1*y2 - x2*y1)
def nrd(x):
    x0,x1,x2,x3 = x
    return x0*x0 - a*x1*x1 - b*x2*x2 + a*b*x3*x3
basis = [(Fr(1),0,0,0),(0,Fr(1),0,0),(Fr(1,2),0,Fr(1,2),0),(0,Fr(1,2),0,Fr(1,2))]
def elt(c): return tuple(sum(Fr(c[t])*basis[t][s] for t in range(4)) for s in range(4))
# coordinates in the O-basis: solve linear system (basis is triangular-ish); use brute inverse
import sympy
Bm = sympy.Matrix([[sympy.Rational(basis[t][s]) for t in range(4)] for s in range(4)])
Binv = Bm.inv()
def coords(x):
    v = Binv * sympy.Matrix([sympy.Rational(c) for c in x])
    assert all(c.q == 1 for c in v), v
    return tuple(int(c) % 3 for c in v)
# check O closed under multiplication
for s in range(4):
    for t in range(4):
        coords(mul(basis[s], basis[t]))
print("O is a ring (closed under products): True; disc check nrd form det:")
G = sympy.Matrix(4,4, lambda s,t: sympy.Rational(nrd(tuple(basis[s][r]+basis[t][r] for r in range(4))) - nrd(basis[s]) - nrd(basis[t])))
print("  det(trace form) =", G.det(), " (expect disc^2 = 36)")
elts = list(product(range(3), repeat=4))
units = [c for c in elts if nrd(elt(c)) % 3 != 0]
n1 = [c for c in units if nrd(elt(c)) % 3 == 1]
print("|O/3O| =", len(elts), " units:", len(units), " norm = 1 mod 3:", len(n1))
# projective image: modulo ±1
print("order of image of O^1 in (O/3O)^*/±1 (assuming strong approx surjectivity):", len(n1)//2)
print("Galois group order of a geometric component of Y_3 -> P^1_j: 4 *", len(n1)//2, "=", 4*len(n1)//2)
