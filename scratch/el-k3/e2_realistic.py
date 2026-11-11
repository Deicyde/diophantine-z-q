"""E2. Realistic admissible B (rs-pole §4.1 sampler: B = 2^4 3^6 5^6 7^6 13^6 u / v^2, u < 1000,
gcd(v,2730) = 1, 0 < B < 1/2). For each multiplier m = 2^f m0 (f<=1, m0 in {1,3,5,7}) with beta odd,
|beta| ≡ 7 (mod 8) (DL's choice set), the one-curve case of X_{beta,theta} (s = ∞) is the curve
C_d, d = beta*theta, with a point of abscissa class beta.  We record: Selmer certificate (exact
2-descent, sel2cong), PARI ellrank bounds and points found, the BSD-heuristic canonical height
of a generator (L'(1) := 1), and a naive search on X with s0 height <= HS, t height <= HT.
Usage: python e2_realistic.py SEED N HS HT
"""
import sys, os, random, time
from fractions import Fraction as Fr
from math import gcd, isqrt, log10
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'descent-alt'))
from common import pari, sqfQ, sqf_int, good, admissible, factor
from e1_points import search

def rand_B(rng):
    K = 2**4 * 3**6 * 5**6 * 7**6 * 13**6
    while True:
        u = rng.randrange(1, 10**3); lo = isqrt(2*K*u) + 1; v = rng.randrange(lo, 4*lo)
        if gcd(v, 2730) == 1:
            B = Fr(K*u, v*v); assert admissible(B); return B

seed, N, HS, HT = map(int, sys.argv[1:5])
rng = random.Random(seed)
for i in range(N):
    B = rand_B(rng)
    for m in (1, 3, 5, 7, 2, 6, 10, 14):
        beta = sqfQ(m*B); theta = sqfQ(m*(m - B))
        if beta % 2 == 0 or abs(beta) % 8 != 7: continue
        d = beta*theta
        t0 = time.time()
        cert = good(d, beta)
        E = pari.ellinit([0, 0, 0, -d*d, 0])
        r = pari.ellrank(E)
        lo, hi, pts = int(r[0]), int(r[1]), r[3]
        hts = [float(pari.ellheight(E, P)) for P in pts]
        om = float(E.omega()[0]) * 2   # two real components (Delta > 0)
        cp = int(pari.ellglobalred(E)[2])
        hest = 16.0 / (om * cp)
        nv = search(beta, theta, HS, HT)
        print(f'B#{i} m={m} beta={beta} theta={theta} ({len(str(theta))} digits, primes {sorted(factor(theta))})', flush=True)
        print(f'    one-curve cert={cert} ellrank=[{lo},{hi}] pts_found={len(pts)} heights={hts} '
              f'BSD-est h(gen)~{hest:.3g} (log10 {log10(hest):.1f}); naive X search: {nv}  [{time.time()-t0:.1f}s]', flush=True)
        break
