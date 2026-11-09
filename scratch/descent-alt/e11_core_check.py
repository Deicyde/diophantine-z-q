"""E11: Proposition B on actual curves.  beta has an isotropic core K (primes = 1 mod 21840, pairwise
residues).  For every multiplier m, check with the exact Selmer code that
dim Sel2(C_{beta_m theta_m}) >= 2(K - omega_odd(theta_m)) + 2, and report whether any m certifies n = beta.
Usage: e11_core_check.py K COUNT SEED"""
import sys, random, time
from common import *
K, count, seed = map(int, sys.argv[1:4])
rng = random.Random(seed)
core = []
p = 1
while len(core) < K:
    p += 21840
    if pari.isprime(p) and all(pow(p, (c - 1) // 2, c) == 1 for c in core):
        core.append(p)
print("core", core, flush=True)
for i in range(count):
    B = gen_with_beta_primes(rng, core, dmult=2)
    t0 = time.time()
    viol = 0; cert = []; maxom = 0; dims = {}
    for m in DIVS:
        beta, theta = beta_theta(B, m)
        if theta == 1:
            cert.append((m, "theta=1")); continue
        om = len(oddprimes(theta)); maxom = max(maxom, om)
        d = sqf_int(beta * theta)
        dim, inpi = info(d, beta)
        dims[dim] = dims.get(dim, 0) + 1
        if dim < 2 * (K - om) + 2:
            viol += 1
        if dim == 3 and inpi:
            cert.append(m)
    print(f"#{i} B={B}\n   max omega(theta_m)={maxom}, bound violations={viol}, dims={dims}, certified m={cert} ({time.time()-t0:.0f}s)", flush=True)
