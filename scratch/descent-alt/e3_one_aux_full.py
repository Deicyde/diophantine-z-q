"""E3: full enumeration of one symbolic auxiliary prime for fixed (B, m): counts of symbol data
making C_{beta q} good, C_{beta q theta} good, both.  Usage: e3_one_aux_full.py SEED COUNT MAXOMEGA"""
import sys, random, time
from common import *
from auxsym import build_cfg, base_L, good_cfg

seed, count, maxom = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
rng = random.Random(seed)
done = 0
while done < count:
    B = gen_random(rng)
    for m in DIVS:
        beta, theta = beta_theta(B, m)
        if beta % 2 == 0 or theta == 1:
            continue
        beta = abs(beta)
        bp = oddprimes(beta); tp = oddprimes(theta)
        base = bp + tp
        if len(base) > maxom:
            continue
        BL = base_L(base); BB = base_L(bp)
        kb = len(bp); um = (1 << kb) - 1
        c1 = c2 = both = 0
        by8 = {}
        for m8 in (1, 3, 5, 7):
            for s in range(1 << len(base)):
                sig = [(s >> i) & 1 for i in range(len(base))]
                g1 = good_cfg(build_cfg(bp, BB, [dict(mod8=m8, sigma=sig[:kb], tau=[])]), um)
                g2 = good_cfg(build_cfg(base, BL, [dict(mod8=m8, sigma=sig, tau=[])]), um)
                c1 += g1; c2 += g2; both += g1 and g2
                if g1 and g2: by8[m8] = by8.get(m8, 0) + 1
        g0 = good_cfg(symsel_cfg := build_cfg(base, BL, []), um)
        print(f"m={m} beta mod 8={beta%8} kb={kb} kt={len(tp)} n=beta ok:{g0} "
              f"one aux: first {c1} second {c2} both {both} of {4<<len(base)} by q mod 8 {by8}", flush=True)
        done += 1
        if done >= count:
            break
