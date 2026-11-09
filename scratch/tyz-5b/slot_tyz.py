"""Row 5b on the curves produced by the slot construction of docs/research/slot-k.md.

mode 'admissible': inputs from slot-k's random generator (run_dl.gen_random, seed 2026), first
  eligible multiplier (or all with ALL=1).  For d in {|n|, |n theta|}: d mod 8, exact descent
  (dim Sel_2, beta in pi_1), det M_5b from Legendre symbols, chi_{-1}(|beta|).
mode 'small': small realizations (primes < 3000, data with (theta1)-(theta4) not from an admissible
  B, as in slot-k t4_ellrank.py).  In addition the TYZ tau(1/2) bracket is computed with PARI class
  groups when omega(d) <= 8.
Usage: slot_tyz.py admissible COUNT  |  slot_tyz.py small COUNT SEED
"""
import os, sys, random
from math import prod
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'slot-k'))
sys.path.insert(0, os.path.join(HERE, '..', 'rv-route-k'))
import cypari2
pari = cypari2.Pari(); pari.allocatemem(2 * 10 ** 9)
import slotk
slotk.JAC = lambda x, q: int(pari.kronecker(x, q))
import sel2cong as S2
from forest_check import det2
from rule_check import smith_M1, tyz_5b

def det5b(ps):
    M, y, z = smith_M1(ps); r = len(ps)
    Mb = [M[i] + [y[i - r] if i >= r else 0] for i in range(2 * r)] + [[0] * r + y + [0]]
    return det2(Mb)

def check_curve(d, ps, beta, do_tyz):
    d = abs(d); ps = sorted(ps)
    basis, gens = S2.selmer(d, ps)
    inpi = S2.first_coord_contains(basis, S2.vec_of(beta, gens))
    rule = sum(1 for p in ps if abs(beta) % p == 0 and p % 4 == 3) % 2
    rec = dict(mod8=d % 8, dim=len(basis), beta_in=inpi, rule=rule, det5b=det5b(ps), omega=len(ps))
    if do_tyz and len(ps) <= 8:
        rec['tyz'] = tyz_5b(ps)
    return rec

def fac(n):
    n = abs(int(n))
    if n <= 1: return {}
    F = pari.factor(n)
    return {int(p): int(e) for p, e in zip(F[0], F[1])}

def admissible(count, all_m):
    import run_dl
    rng = random.Random(2026); bad = 0; ncurves = 0
    for i in range(count):
        B = run_dl.gen_random(rng)
        ms = slotk.choose_m(B, fac)
        for m in (ms if all_m else ms[:1]):
            beta = slotk.sqf(m * B, fac); theta = slotk.sqf(m * (m - B), fac)
            P = sorted(fac(beta)); T = sorted(fac(theta))
            q0, RP, RT = slotk.construct(beta, theta, P, T)
            n = beta * q0 * prod(RP) * prod(RT)
            recs = [check_curve(n, P + [q0] + RP + RT, beta, False),
                    check_curve(n * theta, P + [q0] + RP + RT + T, beta, False)]
            for rc in recs:
                ncurves += 1
                ok = rc['mod8'] == 5 and rc['dim'] == 3 and rc['beta_in'] and rc['rule'] == 1 and rc['det5b'] == 1
                bad += not ok
            print(f"#{i} m={m} beta%8={abs(beta)%8} w(beta)={len(P)} w(theta)={len(T)} "
                  f"C_n:{recs[0]} C_ntheta:{recs[1]}", flush=True)
    print('curves', ncurves, 'failures', bad)

def small(count, seed):
    sys.argv = ['t4', str(seed), '0']
    rng = random.Random(seed)
    PR = [int(p) for p in pari.primes(pari.primepi(200000))][1:]
    leg = slotk.leg
    def least_prime(cond, used):
        for q in PR:
            if q not in used and cond(q): return q
        raise RuntimeError
    bad = 0; ncurves = 0; tyzc = 0; got = 0
    while got < count:
        P = sorted(rng.sample(PR[:40], rng.randint(1, 3)))
        if prod(P) % 8 != 7: continue
        s = rng.randint(0, 1); beta = (-1) ** s * prod(P)
        T = None
        for _ in range(3000):
            T0 = sorted(rng.sample(PR[:150], rng.randint(1, 2)))
            if set(T0) & set(P) or any(l in (3, 5, 7, 13) for l in T0): continue
            th = prod(T0)
            if th % 8 == 1 and all(leg(beta, l) == 0 for l in T0) and all(leg(th, p) == 0 for p in P):
                T = T0; break
        if T is None: continue
        x = (s + 1) % 2; lam = lambda p: 1 if p % 4 == 3 else 0
        p0, Pr = P[0], P[1:]
        sym = {p: (1 + lam(p) * x) % 2 for p in Pr}; sym[p0] = (x + sum(sym.values())) % 2
        for l in T: sym[l] = 0
        used = set(P) | set(T)
        q0 = least_prime(lambda q: q % 8 == 3 and all(leg(q, y) == b for y, b in sym.items()), used); used.add(q0)
        RP = []
        for p in Pr:
            r = least_prime(lambda q: q % 8 == 1 and leg(q, p) == 1 and leg(q, p0) == 1 and
                            all(leg(q, y) == 0 for y in [w for w in P if w not in (p, p0)] + T + [q0] + RP), used)
            used.add(r); RP.append(r)
        RT = []
        for l in T:
            r = least_prime(lambda q: q % 8 == 1 and leg(q, l) == 1 and leg(q, q0) == 1 and
                            all(leg(q, y) == 0 for y in P + [w for w in T if w != l] + RP + RT), used)
            used.add(r); RT.append(r)
        n = beta * q0 * prod(RP) * prod(RT)
        got += 1
        recs = [check_curve(n, P + [q0] + RP + RT, beta, True),
                check_curve(n * prod(T), P + [q0] + RP + RT + T, beta, True)]
        for rc in recs:
            ncurves += 1
            ok = rc['mod8'] == 5 and rc['dim'] == 3 and rc['beta_in'] and rc['rule'] == 1 and rc['det5b'] == 1
            if 'tyz' in rc:
                tyzc += 1; ok = ok and rc['tyz'] == 1
            bad += not ok
        print(f"P={P} T={T} s={s} q0={q0} R_P={RP} R_T={RT} | {recs}", flush=True)
    print('curves', ncurves, 'with PARI TYZ sum', tyzc, 'failures', bad)

if __name__ == '__main__':
    if sys.argv[1] == 'admissible':
        admissible(int(sys.argv[2]), os.environ.get('ALL') == '1')
    else:
        small(int(sys.argv[2]), int(sys.argv[3]))
