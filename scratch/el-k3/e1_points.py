"""E1. Points on X_{beta,theta}: w^2 = theta f(s) f(t), f = beta^2 s^4 - 1, for toy pairs
satisfying (θ1)-(θ4) of cr3-map-needs L4 (|beta| ≡ 7 mod 8 odd, theta ≡ 1 mod 8 squarefree,
coprime to 2730*beta, (beta/l) = 1 for l | theta, (theta/p) = 1 for p | beta).
Search: for s0 in {∞} ∪ {a/b : max(|a|,b) <= HS}, hyperellratpoints(c*(beta^2 x^4 - 1), HT)
with c = sqf(theta*f(s0)). Records the smallest max(H(s0), H(t)) found.
Usage: python e1_points.py SEED N HS HT
"""
import sys, random, time
from fractions import Fraction as Fr
from math import gcd
import cypari2
pari = cypari2.Pari(); pari.allocatemem(2*10**9)

def sqf(n):
    n = int(n); s = -1 if n < 0 else 1
    f = pari.factor(abs(n))
    for p, e in zip(f[0], f[1]):
        if int(e) % 2: s *= int(p)
    return s

def leg(a, p): return int(pari.kronecker(a, p))

def toy_pair(rng, theta_digits):
    while True:
        k = rng.choice([1, 1, 2, 3])
        bps = sorted({int(pari.nextprime(rng.randrange(3, 400))) for _ in range(k)})
        b = 1
        for p in bps: b *= p
        sign = rng.choice([1, -1])
        beta = sign * b
        if abs(beta) % 8 != 7: continue
        # theta: 1 or 2 primes, ≡ 1 mod 8 overall, coprime to 2730*beta, symbol conditions
        for _ in range(2000):
            j = rng.choice([1, 2])
            lo = 10 ** (theta_digits / j - 0.5); hi = 10 ** (theta_digits / j + 0.5)
            ls = [int(pari.nextprime(rng.randrange(int(lo), int(hi)))) for _ in range(j)]
            if len(set(ls)) < j: continue
            th = 1
            for l in ls: th *= l
            if th % 8 != 1 or any(l in (2, 3, 5, 7, 13) or b % l == 0 for l in ls): continue
            if all(leg(beta, l) == 1 for l in ls) and all(leg(th, p) == 1 for p in bps):
                return beta, th, bps, ls

def heights(HS):
    out = []
    for h in range(1, HS + 1):
        for a in range(-h, h + 1):
            for b in range(1, h + 1):
                if max(abs(a), b) == h and gcd(a, b) == 1:
                    out.append((h, Fr(a, b)))
    return out

def search(beta, th, HS, HT):
    best = None
    cands = [(0, None)] + heights(HS)   # s0 = ∞ has height 0 here (torsion first curve)
    for h, s0 in cands:
        if best is not None and h >= best[0]: break
        if s0 is None: c = th
        else:
            fv = Fr(beta**2) * s0**4 - 1
            c = sqf(th * fv.numerator * fv.denominator)
        pts = pari.hyperellratpoints(pari(f'{c}*({beta}^2*x^4-1)'), HT)
        for P in pts:
            t = Fr(int(pari.numerator(P[0])), int(pari.denominator(P[0])))
            ht = max(abs(t.numerator), t.denominator)
            cand = (max(h, ht), s0, t)
            if best is None or cand[0] < best[0]: best = cand
    return best

if __name__ == '__main__':
    seed, N, HS, HT = map(int, sys.argv[1:5])
    rng = random.Random(seed)
    for i in range(N):
        dig = 2 + (i % 6)          # theta of 2..7 digits
        beta, th, bps, ls = toy_pair(rng, dig)
        t0 = time.time()
        best = search(beta, th, HS, HT)
        if best:
            H, s0, t = best
            sv = 'inf' if s0 is None else str(s0)
            # exact check
            def fq(x): return Fr(beta**2) * x**4 - 1 if x is not None else Fr(1)
            val = th * fq(s0) * fq(t)
            assert int(pari.issquare(pari(f'{val.numerator}/{val.denominator}'))) == 1
            res = f'point H={H} s={sv} t={t}'
        else:
            res = 'none'
        print(f'{i:2d} beta={beta} theta={th} primes(theta)={ls} : {res}  [{time.time()-t0:.1f}s]', flush=True)
