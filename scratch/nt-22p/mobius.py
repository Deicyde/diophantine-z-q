"""Moebius transformations of P^1(Q) that map the contact set C into C (or C u {1}, C u {inf})."""
from fractions import Fraction as Fr
from itertools import permutations
C = [Fr(c) for c in (0, -15, -20, -24, -30, -60)]
def mob(src, dst):
    # the Moebius map sending src[i] -> dst[i] (finite points), as a matrix
    (z1, z2, z3), (w1, w2, w3) = src, dst
    # cross-ratio matrix M_z sends z1,z2,z3 -> 0, inf, 1 ... use (z - z1)(z3 - z2)/((z - z2)(z3 - z1))
    def m(a, b, c): return [[c - b, -a*(c - b)], [c - a, -b*(c - a)]]
    A, B = m(z1, z2, z3), m(w1, w2, w3)
    det = B[0][0]*B[1][1] - B[0][1]*B[1][0]
    Binv = [[B[1][1], -B[0][1]], [-B[1][0], B[0][0]]]
    return [[sum(Binv[i][k]*A[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
def apply(M, z):
    num, den = M[0][0]*z + M[0][1], M[1][0]*z + M[1][1]
    return None if den == 0 else num/den
found = set()
for tgt_name, T in [("C", C), ("C+{1}", C + [Fr(1)])]:
    for src in [tuple(C[:3])]:
        for dst in permutations(T, 3):
            M = mob(src, dst)
            img = [apply(M, z) for z in C]
            if all(x is not None and x in T for x in img) and len(set(img)) == 6:
                key = tuple(img)
                if key not in found:
                    found.add(key); print(tgt_name, "C ->", [str(x) for x in img])
print("nontrivial maps found:", len(found) - 1)
