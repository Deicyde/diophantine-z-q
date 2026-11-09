"""Larger-budget retry of the K-TYZ-beta search for one input B (given as a fraction N/D).
For every rule-compatible multiplier: random k-subsets (k = 1..KMAX) of the first POOL primes
>= 11 coprime to beta*theta, residue and necessary-condition filters as in ktyz_beta_search.py,
up to MAXE Selmer evaluations per multiplier.  For comparison the same search without the
beta-rule (Kriz form, any multiplier, n' in any class) is run with the same budget.
Usage: ktyz_retry.py N/D MAXE KMAX POOL SEED"""
import sys, os, random
from fractions import Fraction as Fr
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'rv-route-k'))
import descent_search as ds
from smith22_check import run


def beta_rule(beta):
    ev = beta % 2 == 0
    m3 = (abs(beta) // (2 if ev else 1)) % 4 == 3
    return (['5'] if (not ev and m3) else []) + (['6'] if ev != m3 else [])


B = Fr(sys.argv[1]); maxe, kmax, poolsz, seed = map(int, sys.argv[2:6])
assert ds.admissible(B)
rng = random.Random(seed)
pool_all = [q for q in ds.BIGPOOL if q >= 11][:poolsz]


def search(m, rule):
    beta = ds.sqfQ(m * B); theta = ds.sqfQ(m * (m - B))
    if theta == 1:
        return 'theta=1', 0
    pool = [q for q in pool_all if beta % q and theta % q]
    evals = tries = 0
    while evals < maxe and tries < 200 * maxe:
        tries += 1
        k = rng.randint(1, kmax)
        combo = rng.sample(pool, k)
        npr = 1
        for q in combo:
            npr *= q
        if rule == '6' and beta % 2:
            npr *= 2
        if rule in ('5', '6'):
            if (abs(beta) * npr) % 8 != (5 if rule == '5' else 6):
                continue
        elif rule == 'K' and rng.random() < 0.3:
            npr *= 2
        if not ds.necessary(npr, combo, beta):
            continue
        n = beta * npr; nt = ds.sqf_int(n * theta)
        evals += 1
        g1 = ds.good(n, beta); g2 = ds.good(nt, beta)
        if rule == 'K':
            if g1 and g2:
                return dict(nprime=npr, k=len(combo), g=(g1, g2)), evals
        elif g1 == 'selmer3' and g2 == 'selmer3':
            row = '5b' if rule == '5' else '6'
            ok = run(abs(n), sums=False)[1][row] == 1 and run(abs(nt), sums=False)[1][row] == 1
            return dict(nprime=npr, k=len(combo), tyz_both=ok), evals
    return None, evals


print("B =", B)
for m in ds.DIVS:
    beta = ds.sqfQ(m * B); theta = ds.sqfQ(m * (m - B))
    for rule in beta_rule(beta):
        r, e = search(m, rule)
        print(f"m={m} rule={rule} omega(beta)={len(ds.factor(beta))} omega(theta)={len(ds.factor(theta))}: {r} after {e} evals", flush=True)
print("Kriz-form comparison (any multiplier, any class of n'):")
for m in ds.DIVS[:64]:
    r, e = search(m, 'K')
    if r:
        print(f"  m={m}: {r} after {e} evals", flush=True)
        break
else:
    print("  none found")
