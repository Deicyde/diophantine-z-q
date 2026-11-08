"""Sanity check of selmer_space against PARI's ellrank on small twists."""
import random
from selmer_descent import selmer_dim, pari
rng = random.Random(3)
for fam, (a, b) in [("cong", (1, -1)), ("pi3", (1, -3))]:
    for N in [1, 5, 6, 7, 11, 13, 14, 23, 34, 35, 41, 47, 59, 65, 71, 83, 95, 101, 119]:
        d, gens, ker = selmer_dim(N, a, b, rng)
        E = pari.ellinit([0, -(a + b) * N, 0, a * b * N * N, 0])
        r = pari.ellrank(E)
        print(fam, N, "dim Sel2 =", d, " ellrank:", r[0], r[1], r[2])
