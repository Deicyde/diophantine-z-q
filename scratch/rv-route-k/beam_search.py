"""Beam search for auxiliary primes for a fixed (B, m): minimize the Selmer excess
  score(n') = sum over d in {beta n', sqf(beta n' theta)} of (dim Sel_2(C_d) - 3) + 4 [class beta absent]
(score 0 for a curve where beta = +-d is torsion), adding one prime q at a time from a large pool.

Usage: python beam_search.py B m [width] [cands] [steps] [seed]
"""
import sys
import random
from fractions import Fraction as Fr
from descent_search import sqfQ, sqf_int, factor, oddprimes
from sel2cong import selmer, vec_of, first_coord_contains
import cypari2

pari = cypari2.Pari()
POOL = [int(p) for p in pari.primes(80000)][6:]  # primes 17 .. about 10^6


def curve_score(d, beta):
    if sqf_int(beta * d) == 1 or sqf_int(-beta * d) == 1:
        return 0
    basis, gens = selmer(d, oddprimes(d))
    has = first_coord_contains(basis, vec_of(beta, gens))
    return (len(basis) - 3) + (0 if has else 4)


def score(nprime, beta, theta):
    n = beta * nprime
    return curve_score(n, beta) + curve_score(sqf_int(n * theta), beta)


def beam(B, m, width=4, cands=600, steps=10, seed=0):
    rng = random.Random(seed)
    beta = sqfQ(m * B)
    theta = sqfQ(m * (m - B))
    if theta == 1:
        return 1, 0
    bad = set(factor(beta)) | set(factor(theta))
    states = [(score(1, beta, theta), 1)]
    if states[0][0] == 0:
        return 1, 0
    for step in range(1, steps + 1):
        new = []
        for sc, npr in states:
            for q in rng.sample(POOL, cands):
                if q in bad or npr % q == 0:
                    continue
                s = score(npr * q, beta, theta)
                if s == 0:
                    return npr * q, step
                new.append((s, npr * q))
        new.sort()
        seen, states = set(), []
        for s, npr in new:
            if npr not in seen:
                states.append((s, npr))
                seen.add(npr)
            if len(states) >= width:
                break
        print(f"  step {step}: best scores {[s for s, _ in states]}", flush=True)
    return None, steps


if __name__ == "__main__":
    B = Fr(sys.argv[1])
    m = int(sys.argv[2])
    width = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    cands = int(sys.argv[4]) if len(sys.argv) > 4 else 600
    steps = int(sys.argv[5]) if len(sys.argv) > 5 else 10
    seed = int(sys.argv[6]) if len(sys.argv) > 6 else 0
    beta = sqfQ(m * B)
    theta = sqfQ(m * (m - B))
    print("beta", beta, "theta primes", sorted(factor(theta)))
    res, k = beam(B, m, width, cands, steps, seed)
    print("RESULT", "found n' =" if res else "not found", res, "with", k, "aux primes")
