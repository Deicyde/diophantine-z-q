"""E6: random symbolic auxiliary sets.  For admissible B and each multiplier m with beta odd and
beta = 5 or 7 (8), sample symbolic data for r auxiliary primes and test both curves.
 family 'free': q mod 8 and all symbols random;
 family 'sym' : q = 1 (8), (n'/p) = 1 for p | beta and (beta/q) = 1 for each q (decoupled form).
Reports, per input, the least r (over all such m) with a success among SAMP samples.
Usage: e6_family.py GEN COUNT SEED RMAX SAMP FAMILY"""
import sys, random, time
from common import *
from auxsym import build_cfg, base_L, good_cfg

if __name__ == "__main__":
    gen, count, seed, RMAX, SAMP, fam = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
else:
    gen, count, seed, RMAX, SAMP, fam = "random", 0, 0, 0, 0, "free"
rng = random.Random(seed)
P3 = [p for p in map(int, pari.primes(300)) if p % 4 == 3 and p > 13]


def sample_aux(r, kb, kt, rng):
    aux = []
    for t in range(r):
        if fam == "free":
            m8 = rng.choice((1, 3, 5, 7))
            sb = [rng.randrange(2) for _ in range(kb)]
        else:
            m8 = 1
            sb = [rng.randrange(2) for _ in range(kb)]
        st = [rng.randrange(2) for _ in range(kt)]
        aux.append(dict(mod8=m8, sigma=sb + st, tau=[rng.randrange(2) for _ in range(t)]))
    if fam == "sym":
        # (beta/q) = 1: row parity of sigma_B even for each q  (q = 1 mod 4 so (p/q) = (q/p))
        for a in aux:
            if sum(a["sigma"][:kb]) % 2:
                a["sigma"][rng.randrange(kb)] ^= 1
        # (n'/p) = 1 for each p | beta: column parities even -> fix with the last aux prime, then
        # re-fix its row parity using a second coordinate if needed
        if r >= 1:
            for i in range(kb):
                if sum(a["sigma"][i] for a in aux) % 2:
                    aux[-1]["sigma"][i] ^= 1
            if sum(aux[-1]["sigma"][:kb]) % 2:
                return None  # inconsistent parity (sum of column parities = sum of row parities)
    return aux


def solve(beta, theta):
    bp = oddprimes(beta); tp = oddprimes(theta)
    kb, kt = len(bp), len(tp)
    base = bp + tp
    BL = base_L(base); BB = base_L(bp)
    um = (1 << kb) - 1
    if good_cfg(build_cfg(base, BL, []), um):
        return 0
    for r in range(1, RMAX + 1):
        for _ in range(SAMP):
            aux = sample_aux(r, kb, kt, rng)
            if aux is None:
                continue
            a1 = [dict(mod8=a["mod8"], sigma=a["sigma"][:kb], tau=a["tau"]) for a in aux]
            if not good_cfg(build_cfg(bp, BB, a1), um):
                continue
            if good_cfg(build_cfg(base, BL, aux), um):
                return r
    return None

if __name__ != "__main__":
    count = 0
for i in range(count):
    if gen == "random":
        B = gen_random(rng)
    else:
        B = gen_with_beta_primes(rng, rng.sample(P3, int(gen[3:])))
    t0 = time.time()
    best = None; per = {}
    for m in DIVS:
        beta, theta = beta_theta(B, m)
        if beta % 2 == 0 or theta == 1 or abs(beta) % 8 not in (5, 7):
            continue
        r = solve(abs(beta), theta)
        per[m] = r
        if r is not None and (best is None or r < best):
            best = r
    hist = {}
    for v in per.values():
        hist[v] = hist.get(v, 0) + 1
    print(f"#{i} omega(beta_1)={len(oddprimes(sqfQ(B)))} least r over m = {best}; per-m least r histogram {hist} ({time.time()-t0:.0f}s)", flush=True)
