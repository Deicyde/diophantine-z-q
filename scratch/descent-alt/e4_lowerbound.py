"""E4: lower bound on the number of auxiliary primes.  Core primes p = 1 mod 8*3*5*7*13, pairwise
quadratic residues.  beta = core * s with s an odd product of S0 primes (the multiplier's effect).
Claim: for r >= 1 auxiliary primes, C_{beta n'} good (dim Sel2 = 3, class beta) forces r >= k.
Exhaustive over symbolic data of r auxiliary primes.  Usage: e4_lowerbound.py K RMAX"""
import sys, itertools
from common import *
from auxsym import build_cfg, base_L, good_cfg

K, RMAX = int(sys.argv[1]), int(sys.argv[2])
core = []
p = 1
while len(core) < K:
    p += 21840
    if pari.isprime(p) and all(pow(p, (c - 1) // 2, c) == 1 for c in core):
        core.append(p)
print("core", core)
SL = [int(x) for x in sys.argv[3].split(",")] if len(sys.argv) > 3 else [1, 3, 5, 7, 13, 15, 21, 35, 39, 65, 91, 105, 195, 273, 455, 1365]
for s in SL:
    bp = sorted(core + [x for x in (3, 5, 7, 13) if s % x == 0])
    BB = base_L(bp)
    um = (1 << len(bp)) - 1
    kb = len(bp)
    res = {}
    for r in range(1, RMAX + 1):
        found = 0
        # enumerate: each aux: mod8 (4) x sigma (2^kb); mutual tau (2^{r(r-1)/2})
        auxspace = [(m8, sg) for m8 in (1, 3, 5, 7) for sg in range(1 << kb)]
        for combo in itertools.product(auxspace, repeat=r):
            if any(combo[i] > combo[i + 1] for i in range(r - 1)):
                continue  # symmetric up to order (tau handled fully below)
            for tau in range(1 << (r * (r - 1) // 2)):
                aux = []
                bit = 0
                for t, (m8, sg) in enumerate(combo):
                    tl = []
                    for _ in range(t):
                        tl.append(tau >> bit & 1); bit += 1
                    aux.append(dict(mod8=m8, sigma=[sg >> i & 1 for i in range(kb)], tau=tl))
                if good_cfg(build_cfg(bp, BB, aux), um):
                    found += 1
        res[r] = found
    print(f"s={s} beta mod 8={(s*1)%8} kb={kb}: good counts by r: {res}", flush=True)
