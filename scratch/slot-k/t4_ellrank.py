"""Independent check with PARI ellrank on small realizations of the construction.
Data (beta, theta) with (theta1)-(theta4) are built from small primes (not from admissible B);
slots are the least primes with the prescribed symbols.  For C_n and C_{n theta} we print
ellrank's [r, R, s] and whether a point with x in beta*Q^2 is found among the generators."""
import sys, random, itertools
import cypari2
pari = cypari2.Pari(); pari.allocatemem(4 * 10 ** 9)
from math import prod

def leg(a, p): return 0 if pow(a % p, (p - 1) // 2, p) == 1 else 1
PR = [int(p) for p in pari.primes(3000)][1:]

def least_prime(cond, used, start=3):
    for q in PR:
        if q not in used and cond(q): return q
    raise RuntimeError

def issq_class(x, beta):
    """is x in beta * Q^2 ?"""
    r = pari(x) / beta
    return int(pari.issquare(r)) == 1

def one(rng):
    while True:
        P = sorted(rng.sample(PR[:40], rng.randint(1, 2)))
        if prod(P) % 8 == 7: break
    s = rng.randint(0, 1); beta = (-1) ** s * prod(P)
    for _ in range(2000):
        T = sorted(rng.sample(PR[:120], rng.randint(0, 2)))
        if set(T) & set(P) or any(l in (3, 5, 7, 13) for l in T): continue
        th = prod(T)
        if th % 8 == 1 and all(leg(beta, l) == 0 for l in T) and all(leg(th, p) == 0 for p in P):
            break
    else:
        return None
    x = (s + 1) % 2; lam = lambda p: 1 if p % 4 == 3 else 0
    p0, Pr = P[0], P[1:]
    sym = {p: (1 + lam(p) * x) % 2 for p in Pr}; sym[p0] = (x + sum(sym.values())) % 2
    for l in T: sym[l] = 0
    used = set(P) | set(T)
    q0 = least_prime(lambda q: q % 8 == 3 and all(leg(q, y) == b for y, b in sym.items()), used); used.add(q0)
    RP = []
    for p in Pr:
        r = least_prime(lambda q: q % 8 == 1 and leg(q, p) == 1 and leg(q, p0) == 1 and
                        all(leg(q, y) == 0 for y in [z for z in P if z not in (p, p0)] + T + [q0] + RP), used)
        used.add(r); RP.append(r)
    RT = []
    for l in T:
        r = least_prime(lambda q: q % 8 == 1 and leg(q, l) == 1 and leg(q, q0) == 1 and
                        all(leg(q, y) == 0 for y in P + [z for z in T if z != l] + RP + RT), used)
        used.add(r); RT.append(r)
    n = beta * q0 * prod(RP) * prod(RT)
    out = []
    for d in (n, n * prod(T)):
        E = pari.ellinit([0, 0, 0, -d * d, 0])
        rk = pari.ellrank(E, EFFORT)
        r, R, sel = int(rk[0]), int(rk[1]), int(rk[2])
        pts = rk[3]
        hit = False
        # beta class among x-classes of P + torsion: x(P), x(P+T_i)
        tors = [[0, 0], [d, 0], [-d, 0]]
        for Pt in pts:
            cands = [Pt] + [pari.elladd(E, Pt, t) for t in tors]
            for c in cands:
                if len(c) == 2 and c[0] != 0 and issq_class(c[0], beta): hit = True
        out.append((d, r, R, sel, hit, len(pts)))
    return P, T, s, q0, RP, RT, out

EFFORT = int(sys.argv[3]) if len(sys.argv) > 3 else 4
rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 3)
N = int(sys.argv[2]) if len(sys.argv) > 2 else 10
good = 0; tot = 0
for i in range(N):
    res = one(rng)
    if res is None: continue
    P, T, s, q0, RP, RT, out = res
    tot += 1
    ok = all(o[1] == 1 and o[2] == 1 and o[4] for o in out)
    good += ok
    print(f"P={P} T={T} s={s} q0={q0} R_P={RP} R_T={RT} | " +
          " ; ".join(f"d={o[0]} rank in [{o[1]},{o[2]}] points={o[5]} beta-point={o[4]}" for o in out), flush=True)
print(f"ellrank: {good}/{tot} with rank exactly 1 on both curves and a point with x in beta Q*^2")
