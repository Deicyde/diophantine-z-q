"""Distribution of s(beta q) - s(beta) over all symbolic single primes q (s = dim Sel2 - 2)."""
import sys, random
from common import *
from auxsym import build_cfg, base_L
import symsel
from collections import Counter
rng = random.Random(int(sys.argv[1]))
pr = [int(p) for p in pari.primes(300)][1:]
drop = Counter(); mindrop = Counter()
for t in range(int(sys.argv[2])):
    k = rng.randint(1, 7)
    bp = sorted(rng.sample(pr, k))
    BB = base_L(bp)
    s0 = symsel.selmer_dim(symsel.config_of(bp)) - 2
    best = 99
    for m8 in (1, 3, 5, 7):
        for s in range(1 << k):
            sig = [(s >> i) & 1 for i in range(k)]
            s1 = symsel.selmer_dim(build_cfg(bp, BB, [dict(mod8=m8, sigma=sig, tau=[])])) - 2
            drop[s1 - s0] += 1
            best = min(best, s1 - s0)
    mindrop[(s0, best)] += 1
print("s(beta q) - s(beta) histogram:", sorted(drop.items()))
print("(s(beta), min over q of change):", sorted(mindrop.items()))
