"""E8: is there always a single auxiliary prime that lowers the potential
   Phi = phi(C_{beta n'}) + phi(C_{beta n' theta}),  phi(C_d) = dim Sel2 - 3 if beta in pi1, else dim Sel2 - 1
(phi >= 0, = 0 iff good)?  Greedy descent with full enumeration of one new symbolic prime per
step (q mod 8, symbols to all earlier primes).  Usage: e8_greedy.py GEN COUNT SEED MAXK"""
import sys, random, time
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "descent-alt"))
from common import *
from auxsym import build_cfg, base_L
import symsel

gen, count, seed, MAXK = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
MAXR = int(sys.argv[5]) if len(sys.argv) > 5 else 5
rng = random.Random(seed)
P3 = [p for p in map(int, pari.primes(300)) if p % 4 == 3 and p > 13]


def phi(cfg, um):
    rows, n = symsel.equations(cfg)
    dim = len(symsel.kernel(rows, n))
    return dim - 3 if symsel.has_first(cfg, um) else dim - 1


def Phi(bp, BB, base, BL, aux, um, pair=False):
    a1 = [dict(mod8=a["mod8"], sigma=a["sigma"][:len(bp)], tau=a["tau"]) for a in aux]
    p1 = 0 if not aux else phi(build_cfg(bp, BB, a1), um)   # n' = 1: torsion point on C_beta
    p2 = phi(build_cfg(base, BL, aux), um)
    return (p1, p2) if pair else p1 + p2


def run(beta, theta):
    bp = oddprimes(beta); tp = oddprimes(theta)
    base = bp + tp; kb = len(bp)
    BL = base_L(base); BB = base_L(bp); um = (1 << kb) - 1
    aux = []
    cur = Phi(bp, BB, base, BL, aux, um)
    trace = [Phi(bp, BB, base, BL, aux, um, True)]
    while cur > 0 and len(aux) < MAXR:
        r = len(aux)
        best = None
        for m8 in (1, 3, 5, 7):
            for s in range(1 << len(base)):
                for tau in range(1 << r):
                    a = dict(mod8=m8, sigma=[s >> i & 1 for i in range(len(base))],
                             tau=[tau >> j & 1 for j in range(r)])
                    v = Phi(bp, BB, base, BL, aux + [a], um)
                    if best is None or v < best[0]:
                        best = (v, [a])
                    elif v == best[0]:
                        best[1].append(a)
        aux.append(rng.choice(best[1])); cur = best[0]
        trace.append(Phi(bp, BB, base, BL, aux, um, True))
    return trace

for i in range(count):
    while True:
        B = gen_random(rng) if gen == "random" else gen_with_beta_primes(rng, rng.sample(P3, int(gen[3:])))
        ms = [m for m in DIVS if beta_theta(B, m)[0] % 2 and beta_theta(B, m)[1] != 1
              and abs(beta_theta(B, m)[0]) % 8 in (5, 7)
              and len(oddprimes(beta_theta(B, m)[0])) + len(oddprimes(beta_theta(B, m)[1])) <= MAXK]
        if ms:
            break
    m = rng.choice(ms)
    beta, theta = beta_theta(B, m)
    t0 = time.time()
    tr = run(abs(beta), theta)
    fallback = ""
    if tr[-1] != (0, 0):
        import e6_family as E
        E.RMAX, E.SAMP, E.fam, E.rng = 6, 3000, "free", random.Random(seed + i)
        fallback = f" random-search least r = {E.solve(abs(beta), theta)}"
    print(f"#{i} B={B} m={m} kb={len(oddprimes(beta))} kt={len(oddprimes(theta))} beta mod 8={abs(beta)%8} Phi trace {tr}{fallback} ({time.time()-t0:.0f}s)", flush=True)
