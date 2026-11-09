"""E2: one auxiliary prime, all symbol vectors.  For admissible B and multipliers m with beta odd,
count the symbol data (q mod 8, sigma) for which both C_{beta q} and C_{beta q theta} are good.
Also record whether n = beta already works.  Usage: e2_one_aux.py FAMILY COUNT SEED [MAXSAMPLES]"""
import sys, random, time, itertools
from common import *
from auxsym import build_cfg, base_L, good_cfg

fam, count, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
maxs = int(sys.argv[4]) if len(sys.argv) > 4 else 4096
rng = random.Random(seed)
P3 = [p for p in map(int, pari.primes(300)) if p % 4 == 3 and p > 13]


def analyse(beta, theta):
    bp = oddprimes(beta); tp = oddprimes(theta)
    base = bp + tp
    BL = base_L(base)
    kb = len(bp)
    umask = (1 << kb) - 1          # beta's primes are the first kb
    found = 0; tried = 0
    space = [(m8, s) for m8 in (1, 3, 5, 7) for s in range(1 << len(base))]
    if len(space) > maxs:
        space = rng.sample(space, maxs)
    for m8, s in space:
        sig = [(s >> i) & 1 for i in range(len(base))]
        aux = [dict(mod8=m8, sigma=sig[:kb], tau=[])]
        c1 = build_cfg(bp, base_L(bp), aux)
        # in c1 the aux prime is index kb; beta mask unchanged
        if not good_cfg(c1, umask):
            continue
        c2 = build_cfg(base, BL, [dict(mod8=m8, sigma=sig, tau=[])])
        tried += 1
        if good_cfg(c2, umask):
            found += 1
    return found, len(space)

for i in range(count):
    if fam == "random":
        B = gen_random(rng)
    else:
        B = gen_with_beta_primes(rng, rng.sample(P3, int(fam[3:])))
    t0 = time.time()
    res = []
    for m in DIVS:
        beta, theta = beta_theta(B, m)
        if beta % 2 == 0 or theta == 1:
            continue
        beta = abs(beta)
        f, tot = analyse(beta, theta)
        res.append((m, f, tot))
    nm = sum(1 for r in res if r[1] > 0)
    print(f"#{i} omega(beta_1)={len(oddprimes(sqfQ(B)))} multipliers with a working single aux prime: {nm}/{len(res)}; "
          f"worst {min(r[1]/r[2] for r in res):.4f} best {max(r[1]/r[2] for r in res):.4f} "
          f"zero-m: {[r[0] for r in res if r[1]==0]} ({time.time()-t0:.0f}s)", flush=True)
