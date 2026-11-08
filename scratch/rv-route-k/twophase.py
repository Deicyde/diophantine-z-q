"""Two-phase search for a fixed (B, m).
Phase 1: random n' (1..6 primes from a pool up to 10^6, necessary odd-prime conditions) until the
class beta lies in Sel_2 of both C_n and C_{n theta}.  Phase 2: beam search adding primes that keep
the class on both curves and lower dim Sel_2(C_n) + dim Sel_2(C_{n theta}) to 3 + 3.
Usage: python twophase.py B m   (or: python twophase.py --list FILE, lines "B m")"""
import sys, random
from fractions import Fraction as Fr
from descent_search import sqfQ, sqf_int, factor, oddprimes, necessary
from sel2cong import selmer, vec_of, first_coord_contains
from beam_search import POOL


def state(nprime, beta, theta):
    res = []
    for d in (beta * nprime, sqf_int(beta * nprime * theta)):
        if sqf_int(beta * d) == 1 or sqf_int(-beta * d) == 1:
            res.append((3, True))
            continue
        b, g = selmer(d, oddprimes(d))
        res.append((len(b), first_coord_contains(b, vec_of(beta, g))))
    return res


def solve(B, m, seed=0, p1_trials=20000, width=6, cands=400, steps=8):
    rng = random.Random(seed)
    beta = sqfQ(m * B); theta = sqfQ(m * (m - B))
    if theta == 1:
        return "theta=1", 1
    bad = set(factor(beta)) | set(factor(theta))
    starts = []
    t = 0
    while t < p1_trials and len(starts) < width:
        k = rng.randint(1, 6)
        combo = [q for q in rng.sample(POOL, k) if q not in bad]
        prod = 1
        for q in combo: prod *= q
        if not necessary(prod, combo, beta):
            continue
        t += 1
        s = state(prod, beta, theta)
        if s[0][1] and s[1][1]:
            if s[0][0] == 3 and s[1][0] == 3:
                return "phase1", prod
            starts.append((s[0][0] + s[1][0], prod))
    if not starts:
        return None, f"phase 1 found no n' with the class on both curves in {t} trials"
    states = sorted(starts)[:width]
    for step in range(steps):
        new = []
        for sc, npr in states:
            for q in rng.sample(POOL, cands):
                if q in bad or npr % q == 0:
                    continue
                prod = npr * q
                if not necessary(prod, [p for p in factor(prod)], beta):
                    continue
                s = state(prod, beta, theta)
                if s[0][1] and s[1][1]:
                    if s[0][0] == 3 and s[1][0] == 3:
                        return "phase2", prod
                    new.append((s[0][0] + s[1][0], prod))
        if not new:
            break
        new.sort()
        states = new[:width]
    return None, f"phase 2 stuck; best dims sum {states[0][0] if states else None}"


if __name__ == "__main__":
    if sys.argv[1] == "--list":
        pairs = [l.split() for l in open(sys.argv[2]) if l.strip()]
    else:
        pairs = [(sys.argv[1], sys.argv[2])]
    ok = 0
    for Bs, ms in pairs:
        B, m = Fr(Bs), int(ms)
        how, npr = solve(B, m)
        ok += how is not None
        print(f"m={m} B={Bs[:24]}...: {how} n'={npr} omega(n')={len(factor(npr)) if how else '-'}", flush=True)
    print("solved", ok, "of", len(pairs))
