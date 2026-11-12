"""Ground truth for Gamma1Genus.lean: genus of X_1(N) from the action of S, ST, T on
SL2(Z)/±Γ1(N) ≅ {primitive (a,c) in (Z/N)^2}/± (first column), versus closed forms.
Sample: N = 1..30 (30 inputs, run sequentially)."""
from math import gcd
from fractions import Fraction
from sympy import totient, divisors, primefactors

def cosets(N):
    pts = set()
    for a in range(N):
        for c in range(N):
            if gcd(gcd(a, c), N) == 1:
                pts.add(min((a % N, c % N), ((-a) % N, (-c) % N)))
    return pts

def canon(v, N):
    a, c = v[0] % N, v[1] % N
    return min((a, c), ((-a) % N, (-c) % N))

def data(N):
    if N == 1:
        X = {(0, 0)}
        S = lambda v: v; T = lambda v: v; ST = lambda v: v
    else:
        X = cosets(N)
        S = lambda v: canon((-v[1], v[0]), N)
        T = lambda v: canon((v[0] + v[1], v[1]), N)
        ST = lambda v: canon((-v[1], v[0] + v[1]), N)
    mu = len(X)
    nu2 = sum(1 for v in X if S(v) == v)
    nu3 = sum(1 for v in X if ST(v) == v)
    seen, orbits = set(), 0
    for v in X:
        if v in seen: continue
        orbits += 1
        w = v
        while w not in seen:
            seen.add(w); w = T(w)
    g = 1 + Fraction(mu, 12) - Fraction(nu2, 4) - Fraction(nu3, 3) - Fraction(orbits, 2)
    return mu, nu2, nu3, orbits, g

def closed(N):
    J2 = N * N
    for p in primefactors(N): J2 = J2 * (p * p - 1) // (p * p)
    mu = J2 // 2 if N >= 3 else (1 if N == 1 else 3)
    cusps = sum(totient(d) * totient(N // d) for d in divisors(N)) // 2 if N >= 5 else None
    return mu, cusps

# Genus table of X_1(N), N = 1..30, from memory (UNVERIFIED reference values; e.g. LMFDB / Cremona)
TABLE = {**{n: 0 for n in range(1, 11)}, 11: 1, 12: 0, 13: 2, 14: 1, 15: 1, 16: 2, 17: 5, 18: 2,
         19: 7, 20: 3, 21: 5, 22: 6, 23: 12, 24: 5, 25: 12, 26: 10, 27: 13, 28: 10, 29: 22, 30: 9}

for N in range(1, 31):
    mu, n2, n3, ninf, g = data(N)
    cmu, ccusps = closed(N)
    ok = (mu == cmu) and (ccusps is None or ccusps == ninf) and g == TABLE[N] and g <= N * N
    print(N, mu, n2, n3, ninf, g, "ok" if ok else "MISMATCH", "mu<=N^2:", mu <= N * N)
