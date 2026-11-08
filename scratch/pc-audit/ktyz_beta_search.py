"""Route K descent in the K-TYZ-beta form.

For admissible B (generators of scratch/rv-route-k/descent_search.py) search a multiplier m and
n = beta * n' with
   rule 5:  beta odd, |beta| = 3 (mod 4), |n| = 5 (mod 8);   or
   rule 6:  [beta even] != [|beta|_odd = 3 (mod 4)],  |n| = 6 (mod 8),
such that C_n and C_{n theta} are both Selmer-minimal with a class of first coordinate beta
(theta = 1 needs no converse).  Auxiliary primes are >= 11 (so f_0 >= 11), coprime to beta*theta,
drawn at random from primes below 20000 (2 is added when rule 6 needs n' even), and filtered by
the necessary local conditions.  Every solution is re-checked: Smith's determinant (row 5b or 6)
must be nonzero for both curves.
Usage: ktyz_beta_search.py FAMILY COUNT SEED MAXEVALS
"""
import sys, os, random
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'rv-route-k'))
import descent_search as ds
from smith22_check import run


def beta_rule(beta):
    ev = beta % 2 == 0
    m3 = (abs(beta) // (2 if ev else 1)) % 4 == 3
    rules = []
    if not ev and m3:
        rules.append('5')
    if ev != m3:
        rules.append('6')
    return rules


def main():
    fam, count, seed, maxe = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    rng = random.Random(seed)
    gen = ds.GENS[fam]
    pool_all = [q for q in ds.BIGPOOL if q >= 11]
    solved = 0
    tyz_fail = 0
    for it in range(count):
        B = gen(rng)
        res = None
        evals = 0
        cands = []
        for m in ds.DIVS:
            beta = ds.sqfQ(m * B)
            theta = ds.sqfQ(m * (m - B))
            for rule in beta_rule(beta):
                cands.append((m, beta, theta, rule))
        rng.shuffle(cands)
        if os.environ.get('FIXM'):
            # one multiplier fixed in advance: the first (in DIVS order) admitting rule 6 with
            # theta > 1, else rule 5
            fixed = [c for c in sorted(cands, key=lambda c: (c[3] != '6', ds.DIVS.index(c[0])))
                     if c[2] != 1][:1]
            cands = fixed
        # first: theta = 1 cases need no converse
        for m, beta, theta, rule in cands:
            if theta == 1:
                res = dict(m=m, beta=beta, theta=1, kind='theta=1')
                break
        tries = 0
        while res is None and cands and evals < maxe and tries < 50 * maxe:
            tries += 1
            m, beta, theta, rule = cands[tries % len(cands)]
            pool = [q for q in pool_all[:400] if beta % q and theta % q]
            k = rng.randint(1, 4)
            combo = rng.sample(pool, k)
            nprime = 1
            for q in combo:
                nprime *= q
            ev = beta % 2 == 0
            if rule == '6' and not ev:
                nprime *= 2
            target = 5 if rule == '5' else 6
            if (abs(beta) * nprime) % 8 != target:
                continue
            if not ds.necessary(nprime, combo, beta):
                continue
            n = beta * nprime
            nt = ds.sqf_int(n * theta)
            evals += 1
            if ds.good(n, beta) == 'selmer3' and ds.good(nt, beta) == 'selmer3':
                D1 = run(abs(n), sums=False)[1]
                D2 = run(abs(nt), sums=False)[1]
                row = '5b' if rule == '5' else '6'
                ok = D1[row] == 1 and D2[row] == 1
                tyz_fail += not ok
                res = dict(m=m, beta=beta, rule=rule, nprime=nprime, k=len(combo), evals=evals,
                           tyz_row=row, tyz_both=ok, omega_beta=len(ds.factor(beta)),
                           omega_theta=len(ds.factor(theta)))
        solved += res is not None
        print(f"input {it}: {res if res else 'NOT SOLVED after %d evaluations' % evals}", flush=True)
        if os.environ.get('SHOWB'):
            print(f"   B = {B}", flush=True)
    print(f"family {fam}: solved {solved}/{count}; solutions failing the TYZ re-check: {tyz_fail}")


main()
