"""Diagnose (B, m) pairs where the fixed-multiplier stress search fails: for the candidates n = beta*q
that pass the necessary odd-prime conditions, record which of the two curves fails and how
(Selmer dimension, presence of the class beta)."""
import sys
import random
from collections import Counter
from descent_search import (GENS, sqfQ, sqf_int, factor, oddprimes, BIGPOOL, necessary, DIVS)
from sel2cong import selmer, vec_of, first_coord_contains, rep2

fam, count, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
ms = [int(x) for x in sys.argv[4].split(",")] if len(sys.argv) > 4 else [1, 2, 3, 5, 6, 7]
rng = random.Random(seed)


def status(d, beta):
    basis, gens = selmer(d, oddprimes(d))
    has = first_coord_contains(basis, vec_of(beta, gens))
    return len(basis), has


for i in range(count):
    B = GENS[fam](rng)
    for m in ms:
        beta = sqfQ(m * B)
        theta = sqfQ(m * (m - B))
        if theta == 1:
            continue
        c = Counter()
        n_ok = 0
        for q in BIGPOOL[:600]:
            if beta % q == 0 or theta % q == 0 or not necessary(q, [q], beta):
                continue
            n = beta * q
            s1 = status(n, beta)
            s2 = status(sqf_int(n * theta), beta)
            c[(s1, s2)] += 1
            n_ok += (s1 == (3, True) and s2 == (3, True))
        b2 = rep2(beta)
        th8 = theta % 8
        print(f"#{i} m={m} beta 2-adic class {b2} sign {'+' if beta > 0 else '-'} theta mod 16 {theta % 16} "
              f"omega(beta)={len(factor(beta))} omega(theta)={len(factor(theta))} successes={n_ok} "
              f"top outcomes ((dimSel,hasBeta) for C_n, C_ntheta): {c.most_common(4)}", flush=True)
