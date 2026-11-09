"""Test: is the class beta on C_{n theta} (random n') obstructed exactly when beta is not a first
coordinate in Sel_2(C_{beta theta}) (the case n' = 1)?"""
import sys, random
from collections import Counter
from descent_search import GENS, sqfQ, sqf_int, oddprimes
from sel2cong import selmer, vec_of, first_coord_contains
from obstruction_probe import present_on

fam, count, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
rng = random.Random(seed)
tab = Counter()
for i in range(count):
    B = GENS[fam](rng)
    for m in [1, 2, 3, 5, 6, 7, -1, -2]:
        beta = sqfQ(m * B); theta = sqfQ(m * (m - B))
        if theta == 1:
            continue
        d0 = sqf_int(beta * theta)
        b0, g0 = selmer(d0, oddprimes(d0))
        P0 = first_coord_contains(b0, vec_of(beta, g0))
        hn, hnt = present_on(beta, theta, rng, trials=120)
        tab[(P0, hnt > 0)] += 1
        print(f"#{i} m={m} P0={P0} dimSel(C_beta theta)={len(b0)} present(C_n)={hn} present(C_ntheta)={hnt}", flush=True)
print("(P0, ever present on C_ntheta):", dict(tab))
