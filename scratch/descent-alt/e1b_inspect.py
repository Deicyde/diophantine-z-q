"""Inspect the extra Selmer classes of C_{beta theta} when dim Sel2 = 3 but beta is not a first coordinate."""
import sys, random
from common import *
rng = random.Random(int(sys.argv[1]))
shown = 0
while shown < 12:
    B = gen_random(rng)
    for m in DIVS:
        beta, theta = beta_theta(B, m)
        if theta == 1: continue
        d = sqf_int(beta * theta)
        basis, gens = sel(d)
        if len(basis) != 3: continue
        if first_coord_contains(basis, vec_of(beta, gens)): continue
        tors = [(vec_of(d, gens), vec_of(2, gens)), (vec_of(-d, gens), vec_of(-2 * d, gens))]
        def val(mask):
            v = 1
            for i, g in enumerate(gens):
                if mask >> i & 1: v *= g
            return v
        # find a basis element not in torsion span
        tsp = F2Span()
        for a, b in tors: tsp.add(a | (b << len(gens)))
        for a, b in basis:
            if tsp.reduce(a | (b << len(gens))):
                ex = (a, b); break
        a, b = ex
        bp = [p for p in factor(beta) if p != 2]; tp = list(factor(theta))
        print(f"m={m} beta={beta} theta={theta} d mod 8={abs(d)%8} extra=({val(a)},{val(b)}) "
              f"a|beta?{all(p in bp or p==2 or p==-1 for p in factor(abs(val(a))))} "
              f"theta primes mod 8 {[p%8 for p in tp]} beta odd primes mod 8 {[p%8 for p in bp]}")
        shown += 1
        break
