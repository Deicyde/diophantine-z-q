"""Supplement: ellheegner point on C_d, its Kummer image, and whether beta is a first coordinate
of the span with the 2-torsion images.  Usage: python heegner.py d beta"""
import sys
import curves
pari = curves.pari
d, beta = int(sys.argv[1]), int(sys.argv[2])
E = pari.ellinit([-d * d, 0])
P = pari.ellheegner(E)
assert pari.ellisoncurve(E, P)
img = curves.kummer(P, d)
basis = [-1, 2] + sorted(int(p) for p in pari.factor(d)[0])
tors = [(-1, curves.core(-d)), (curves.core(d), 2), (curves.core(-d), curves.core(-2 * d))]
print(d, beta, "height", pari.ellheight(E, P), "kummer", img,
      "beta_in_span", curves.first_coord_in_span([img] + tors, beta, basis), "x", P[0])
