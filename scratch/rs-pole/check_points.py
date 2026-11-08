"""For the small curve C_n of a found pair (n, n*theta), find a generator with PARI and check
that its abscissa class lies in beta * {1, -1, n, -n} (torsion abscissa classes)."""
from fractions import Fraction as F
from selmer_descent import pari, core
for beta, aux in [(29, (5, 31, 43)), (26, (5, 11)), (47, (59,))]:
    n = beta
    for q in aux:
        n *= q
    E = pari.ellinit([0, 0, 0, -n * n, 0])
    r = pari.ellrank(E, 2)
    pts = r[3]
    print("n =", n, "ellrank bounds:", r[0], r[1], "points:", [str(p) for p in pts])
    for P in pts:
        x = F(str(P[0]))
        c = core(x)
        ok = any(core(c * t * beta) == 1 for t in (1, -1, n, -n))
        print("   abscissa class", c, "in beta*torsion classes:", ok)
