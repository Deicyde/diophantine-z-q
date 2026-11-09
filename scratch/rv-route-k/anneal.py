"""Simulated annealing over sets of auxiliary primes for a fixed (B, m).
Objective: (dim Sel_2(C_n) - 3) + (dim Sel_2(C_{n theta}) - 3) + 4 [beta absent on C_n]
           + 4 [beta absent on C_{n theta}] + 4 [necessary odd-prime conditions fail],
with torsion shortcut (score 0) when beta = +-d.  Moves: add / remove / replace one prime.
Usage: python anneal.py B m [iters] [seed]   or   python anneal.py --smooth COUNT SEED [iters]
"""
import sys, math, random
from fractions import Fraction as Fr
from descent_search import sqfQ, sqf_int, factor, oddprimes, necessary, gen_smooththeta, search_m
from sel2cong import selmer, vec_of, first_coord_contains
from beam_search import POOL


def curve(d, beta):
    if sqf_int(beta * d) == 1 or sqf_int(-beta * d) == 1:
        return 0
    b, g = selmer(d, oddprimes(d))
    return (len(b) - 3) + (0 if first_coord_contains(b, vec_of(beta, g)) else 4)


def objective(S, beta, theta):
    prod = 1
    for q in S:
        prod *= q
    pen = 0 if necessary(prod, list(S), beta) else 4
    n = beta * prod
    return curve(n, beta) + curve(sqf_int(n * theta), beta) + pen, prod


def anneal(B, m, iters=6000, seed=0, T0=2.0):
    rng = random.Random(seed)
    beta, theta = sqfQ(m * B), sqfQ(m * (m - B))
    if theta == 1:
        return 1, 0
    bad = set(factor(beta)) | set(factor(theta))
    pool = [q for q in POOL if q not in bad]
    S = []
    cur, prod = objective(S, beta, theta)
    best = cur
    for it in range(iters):
        if cur == 0:
            return prod, it
        T = T0 * (1 - it / iters) + 0.05
        S2 = list(S)
        r = rng.random()
        if not S2 or (r < 0.4 and len(S2) < 14):
            S2.append(rng.choice(pool))
        elif r < 0.6:
            S2.pop(rng.randrange(len(S2)))
        else:
            S2[rng.randrange(len(S2))] = rng.choice(pool)
        if len(set(S2)) != len(S2):
            continue
        new, prod2 = objective(S2, beta, theta)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            S, cur, prod = S2, new, prod2
            best = min(best, cur)
    return None, best


if __name__ == "__main__":
    if sys.argv[1] == "--smooth":
        count, seed = int(sys.argv[2]), int(sys.argv[3])
        iters = int(sys.argv[4]) if len(sys.argv) > 4 else 6000
        rng = random.Random(seed)
        ok = 0
        for i in range(count):
            B = gen_smooththeta(rng)
            beta, theta = sqfQ(B), sqfQ(1 - B)
            r = search_m(B, 1, 0, 200)
            if r:
                res, info = r.get("nprime", 1), "shortcut"
            else:
                res, info = None, None
                for s in range(3):
                    res, info = anneal(B, 1, iters, seed=s)
                    if res:
                        break
            ok += res is not None
            print(f"#{i} omega(beta)={len(factor(beta))} omega(theta)={len(factor(theta))} m=1: "
                  f"{'found n=beta*' + str(res) + ' omega(n)=' + str(len(factor(res))) if res else 'not found, best ' + str(info)}",
                  flush=True)
        print("solved", ok, "of", count)
    else:
        B, m = Fr(sys.argv[1]), int(sys.argv[2])
        iters = int(sys.argv[3]) if len(sys.argv) > 3 else 6000
        seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
        print(anneal(B, m, iters, seed))
