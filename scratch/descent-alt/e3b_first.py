"""Which beta admit a single auxiliary prime q with C_{beta q} good (class beta, dim Sel2 = 3)?
Random odd squarefree beta = 5, 7 (8) and 1, 3 (8); record dim Sel2(C_beta) and the count."""
import sys, random
from common import *
from auxsym import build_cfg, base_L, good_cfg
import symsel
rng = random.Random(int(sys.argv[1]))
pr = [int(p) for p in pari.primes(300)][1:]
from collections import defaultdict
stat = defaultdict(lambda: [0, 0])
for t in range(int(sys.argv[2])):
    k = rng.randint(1, 6)
    bp = sorted(rng.sample(pr, k))
    beta = 1
    for p in bp: beta *= p
    BB = base_L(bp); um = (1 << k) - 1
    c1 = 0
    for m8 in (1, 3, 5, 7):
        for s in range(1 << k):
            sig = [(s >> i) & 1 for i in range(k)]
            c1 += good_cfg(build_cfg(bp, BB, [dict(mod8=m8, sigma=sig, tau=[])]), um)
    cfg0 = symsel.config_of(bp)
    s0 = symsel.selmer_dim(cfg0) - 2
    # 2-rank of class group of Q(sqrt(-beta)) etc is not computed; record s(beta) and p3 count
    key = (beta % 8, s0)
    stat[key][0] += 1
    stat[key][1] += (c1 > 0)
for key in sorted(stat):
    print("beta mod 8, s(beta) =", key, " count", stat[key][0], " with a working q:", stat[key][1])
