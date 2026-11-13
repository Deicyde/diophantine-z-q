"""ts-hecke: finite computations behind HeckeIrreducible (pi_0 of Y_3 and its Galois action).

O = Z<1, i, (1+j)/2, (i+k)/2> in B = (2,-3)_Q, coordinates n = (n0,n1,n2,n3) as in
ZInQKernel/HDecomp/QM/Structures.lean (`ofInt`, `mulCoord`).
"""
from fractions import Fraction as F
from itertools import product

def mulCoord(n, m):  # ofInt n * ofInt m = ofInt (mulCoord n m)  (copied from Structures.lean)
    return (m[0]*n[0] + 2*m[1]*n[1] + 2*m[1]*n[3] - m[2]*n[2] + 2*m[3]*n[3],
            m[0]*n[1] + m[1]*n[0] + m[1]*n[2] - m[2]*n[3] + m[3]*n[2],
            m[0]*n[2] - 2*m[1]*n[3] + m[2]*n[0] + m[2]*n[2] + 2*m[3]*n[1],
            m[0]*n[3] - m[1]*n[2] + m[2]*n[1] + m[2]*n[3] + m[3]*n[0])

def quat(n):  # (x0,x1,x2,x3) on 1,i,j,k
    return (n[0] + F(n[2], 2), n[1] + F(n[3], 2), F(n[2], 2), F(n[3], 2))

def nrd(n):  # i^2 = 2, j^2 = -3, k^2 = 6
    x = quat(n)
    v = x[0]**2 - 2*x[1]**2 + 3*x[2]**2 - 6*x[3]**2
    assert v.denominator == 1
    return int(v)

# sanity: mulCoord agrees with quaternion multiplication
def qmul(x, y):
    a, b = 2, -3
    return (x[0]*y[0] + a*x[1]*y[1] + b*x[2]*y[2] - a*b*x[3]*y[3],
            x[0]*y[1] + x[1]*y[0] - b*x[2]*y[3] + b*x[3]*y[2],
            x[0]*y[2] + x[2]*y[0] + a*x[1]*y[3] - a*x[3]*y[1],
            x[0]*y[3] + x[3]*y[0] + x[1]*y[2] - x[2]*y[1])
for n in product(range(-2, 3), repeat=4):
    for m in [(1, 2, 0, -1), (0, 1, 1, 1), (3, -1, 2, 1)]:
        assert qmul(quat(n), quat(m)) == quat(mulCoord(n, m)), (n, m)
        assert nrd(mulCoord(n, m)) == nrd(n) * nrd(m)
print("mulCoord = quaternion product, nrd multiplicative: OK")

R = [tuple(x) for x in product(range(3), repeat=4)]
red = lambda n: tuple(c % 3 for c in n)
mul3 = lambda a, b: red(mulCoord(a, b))
one = (1, 0, 0, 0)
units = [a for a in R if any(mul3(a, b) == one and mul3(b, a) == one for b in R)]
print("|O/3O| =", len(R), " |(O/3O)^x| =", len(units))
# nrd mod 3 is well defined on O/3O (nrd(a+3b) = nrd(a) mod 3)
nrd3 = {a: nrd(a) % 3 for a in R}
print("nrd mod 3 on units takes values", sorted(set(nrd3[a] for a in units)),
      " counts", {v: sum(1 for a in units if nrd3[a] == v) for v in (1, 2)})
assert all((nrd3[a] != 0) == (a in units) for a in R)

# units of O: elements of small height with nrd = +-1
U = [n for n in product(range(-3, 4), repeat=4) if abs(nrd(n)) == 1]
print("units of O with coords in [-3,3]:", len(U), " with nrd -1:", sum(1 for n in U if nrd(n) == -1))
# image of O^x in (O/3O)^x: closure of reductions under multiplication
img = {one}
frontier = [one]
gens = sorted(set(red(n) for n in U))
while frontier:
    new = []
    for a in frontier:
        for g in gens:
            c = mul3(a, g)
            if c not in img:
                img.add(c); new.append(c)
    frontier = new
print("image of O^x in (O/3O)^x has", len(img), "elements")

# pi_0 over C: orbits of O^x on {+1,-1} x (O/3O)^x, u.(s,a) = (s*nrd(u), a*u^{-1})
# (Y_3(C) = O^x \ (H^{+-} x (O/3O)^x), Shimura; u acts on H^{+-} through det = nrd(u)).
inv = {a: next(b for b in R if mul3(a, b) == one) for a in units}
pts = [(s, a) for s in (1, -1) for a in units]
seen, orbits = set(), []
for p0 in pts:
    if p0 in seen: continue
    orb, st = {p0}, [p0]
    while st:
        s, a = st.pop()
        for n in U:
            q = (s * nrd(n), mul3(a, inv[red(n)]))
            if q not in orb:
                orb.add(q); st.append(q)
    seen |= orb; orbits.append(orb)
print("number of orbits (geometric components of Y_3) =", len(orbits), " sizes", [len(o) for o in orbits])
inv_of = lambda s, a: (s * (1 if nrd3[a] == 1 else -1))
for o in orbits:
    print("  invariant s*nrd(a) on this orbit:", set(inv_of(s, a) for s, a in o))
# complex conjugation: (s, a) -> (-s, a)
cc = lambda p: (-p[0], p[1])
idx = lambda p: next(i for i, o in enumerate(orbits) if p in o)
print("complex conjugation maps orbit 0 to orbit", set(idx(cc(p)) for p in orbits[0]),
      "and orbit 1 to orbit", set(idx(cc(p)) for p in orbits[1]))

# level structures on a fixed (A, iota) over Qbar: eta(1) ranges over A[3] ~ O/3O minus
# non-generators: 72 of 81; Aut(A,iota) contains +-1, so <= 36 classes per pair; twists: 4.
print("level structures per pair:", len(units), "; classes per twist orbit <= 4*72/2 =", 4*72//2)
# Riemann-Hurwitz for one geometric component (degree 72 over P^1_j, indices 4,6,2):
from fractions import Fraction
d = 72
chi = d * (-2 + (1 - Fraction(1, 4)) + (1 - Fraction(1, 6)) + (1 - Fraction(1, 2)))
print("2g-2 =", chi, " g =", (chi + 2) / 2)

# The constant field of the Q-component is Q(zeta_3) = Q(sqrt(-3)) (Weil pairing on A[3]:
# a K-point of Y_3 forces mu_3 in K).  Its defining polynomial over Q and over F_p:
import cypari2
pari = cypari2.Pari()
print("factor x^2+x+1 over Q:", pari("factor(x^2+x+1)"))
for p in [5, 7, 11, 13, 17, 19, 23, 29, 31, 37]:
    f = pari(f"factor(Mod(1,{p})*(x^2+x+1))")
    print(f"  p={p} (p mod 3 = {p%3}): {len(f[0])} factor(s)")
