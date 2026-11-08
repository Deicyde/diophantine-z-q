"""Route K descent search on fresh admissible pole inputs.

For an admissible B (square reduced denominator, 0 < B < 1/2, v_p(B) >= 4 for p in S0) and each
signed divisor m of 2730 put beta = sqf(mB), theta = sqf(m(m - B)) (> 0).  Route K needs a
squarefree n with beta | n such that both C_n and C_{n theta} carry a rational point with
abscissa in beta Q*^2.  We certify this for d in {n, sqf(n theta)} by
  good(d) :  beta = +-d mod squares (a 2-torsion point (+-d, 0) has abscissa +-d), or
             dim Sel_2(C_d) = 3 and some Selmer class has first coordinate beta
             (then Kriz Thm 10.13 + Poonen-Stoll give rank 1, Sha finite, Sha[2] = 0).
theta = 1 is the trivial 2-torsion case.  n ranges over beta * n' with n' = 1, n' = theta, and
products of up to MAXK auxiliary primes from AUX (2 and odd primes < AUXB, coprime to beta).

Usage: python descent_search.py FAMILY COUNT SEED [MAXK]
FAMILY: random | manybeta | smooththeta | edgeS0 | extremeB
"""
import sys
import time
import random
import itertools
from fractions import Fraction as Fr
from math import gcd, isqrt
import cypari2
from sel2cong import selmer, vec_of, first_coord_contains, F2Span

pari = cypari2.Pari()
pari.allocatemem(2 * 10 ** 9)

S0 = [2, 3, 5, 7, 13]
DIVS = sorted({s * a for a in [1, 2, 3, 5, 6, 7, 10, 13, 14, 15, 21, 26, 30, 35, 39, 42, 65, 70,
                              78, 91, 105, 130, 182, 195, 210, 273, 390, 455, 546, 910, 1365, 2730]
               for s in (1, -1)})
assert len(DIVS) == 64

_fac_cache = {}


def factor(n):
    n = abs(int(n))
    if n in _fac_cache:
        return _fac_cache[n]
    f = {int(p): int(e) for p, e in zip(*pari.factor(n))} if n > 1 else {}
    _fac_cache[n] = f
    return f


def sqf_int(n):
    s = -1 if n < 0 else 1
    out = 1
    for p, e in factor(n).items():
        if e % 2:
            out *= p
    return s * out


def sqfQ(r):
    r = Fr(r)
    return sqf_int(r.numerator * r.denominator)


def vpQ(r, p):
    r = Fr(r)
    def v(n):
        n = abs(n); k = 0
        while n % p == 0:
            n //= p; k += 1
        return k
    return v(r.numerator) - v(r.denominator)


def admissible(B):
    B = Fr(B)
    d = B.denominator
    return (isqrt(d) ** 2 == d and 0 < B < Fr(1, 2) and all(vpQ(B, p) >= 4 for p in S0))


def oddprimes(d):
    return sorted(p for p in factor(d) if p != 2)


def good(d, beta):
    """Certified existence of a point with abscissa class beta on C_d (see module doc)."""
    if sqf_int(beta * d) == 1 or sqf_int(-beta * d) == 1:
        return "torsion"
    basis, gens = selmer(d, oddprimes(d))
    if len(basis) != 3:
        return None
    if first_coord_contains(basis, vec_of(beta, gens)):
        return "selmer3"
    return None


PRIMES = [int(p) for p in pari.primes(60)]  # first 60 primes: 2..281


def search_m(B, m, maxk, auxb, forbid_trivial=False):
    A = m * B
    beta = sqfQ(A)
    theta = sqfQ(m * (m - B))
    assert theta > 0
    if theta == 1:
        return dict(m=m, beta=beta, theta=1, n=beta, kind="theta=1", k=0)
    aux = [p for p in PRIMES if p < auxb and beta % p != 0]
    cands = [] if forbid_trivial else [(1, 0), (theta, 0)]
    for k in range(1, maxk + 1):
        if not forbid_trivial and k < maxk:
            continue  # the "first" driver calls k = 0, 1, 2, ... in turn
        for combo in itertools.combinations(aux, k):
            prod = 1
            for p in combo:
                prod *= p
            cands.append((prod, k))
    for nprime, k in cands:
        n = beta * nprime
        if sqf_int(n) != n:
            continue
        g1 = good(n, beta)
        if not g1:
            continue
        ntheta = sqf_int(n * theta)
        g2 = good(ntheta, beta)
        if g2:
            return dict(m=m, beta=beta, theta=theta, n=n, nprime=nprime, kind=(g1, g2), k=k)
    return None


BIGPOOL = [int(p) for p in pari.primes(2300)]  # primes up to about 20000


def leg_ok(a, p):
    """a or -a is a nonzero square mod the odd prime p."""
    a %= p
    return a != 0 and (pow(a, (p - 1) // 2, p) == 1 or pow(-a % p, (p - 1) // 2, p) == 1)


def necessary(nprime, nprimes, beta):
    """Necessary local conditions for a class with first coordinate beta on C_{beta n'} (and on
    C_{beta n' theta}) at the odd primes of beta and of n'."""
    bodd = [p for p in factor(beta) if p != 2]
    return (all(leg_ok(nprime, p) for p in bodd) and
            all(leg_ok(beta, q) for q in nprimes if q != 2))


def search_m_big(B, m, maxcand=4000):
    """Stress search: shortcuts n' = 1, theta forbidden; n' = q or q1 q2 with primes < 20000,
    filtered by the necessary local conditions; at most maxcand Selmer evaluations."""
    A = m * B
    beta = sqfQ(A)
    theta = sqfQ(m * (m - B))
    if theta == 1:
        return dict(kind="theta=1", k=0, nprime=1)
    pool = [q for q in BIGPOOL if beta % q != 0 and theta % q != 0]
    singles = [q for q in pool if necessary(q, [q], beta)]
    evals = 0
    for q in singles:
        n = beta * q
        evals += 1
        if good(n, beta) and good(sqf_int(n * theta), beta):
            return dict(kind="aux", k=1, nprime=q, evals=evals)
        if evals >= maxcand // 2:
            break
    small = pool[:150]
    for q1, q2 in itertools.combinations(small, 2):
        if not necessary(q1 * q2, [q1, q2], beta):
            continue
        n = beta * q1 * q2
        evals += 1
        if good(n, beta) and good(sqf_int(n * theta), beta):
            return dict(kind="aux", k=2, nprime=q1 * q2, evals=evals)
        if evals >= maxcand:
            break
    return None


def search_m_random(B, m, rng, kmax=7, per_k=1500, poolsize=300):
    """Stress search with many auxiliary primes: random k-subsets (k = 1..kmax) of the first
    poolsize admissible primes, filtered by the necessary local conditions on the product."""
    A = m * B
    beta = sqfQ(A)
    theta = sqfQ(m * (m - B))
    if theta == 1:
        return dict(kind="theta=1", k=0, nprime=1)
    pool = [q for q in BIGPOOL if beta % q != 0 and theta % q != 0][:poolsize]
    for k in range(1, kmax + 1):
        seen = set()
        tries = 0
        while tries < per_k:
            combo = tuple(sorted(rng.sample(pool, k)))
            if combo in seen:
                tries += 1
                continue
            seen.add(combo)
            prod = 1
            for q in combo:
                prod *= q
            if not necessary(prod, combo, beta):
                continue
            tries += 1
            n = beta * prod
            if good(n, beta) and good(sqf_int(n * theta), beta):
                return dict(kind="aux", k=k, nprime=prod)
    return None


# ---------------- input generators (fresh, independent of the rs-pole sampler) ----------------

def rand_coprime(rng, lo, hi, N):
    while True:
        D = rng.randrange(lo, hi)
        if gcd(D, N) == 1:
            return D


def gen_random(rng):
    """N = prod_{S0} p^{e_p} * u with e_p in 4..7, u < 10^7 coprime to 2730; D coprime, B < 1/2."""
    while True:
        base = 1
        for p in S0:
            base *= p ** rng.randint(4, 7)
        u = rng.randrange(1, 10 ** 7)
        if gcd(u, 2730) != 1:
            continue
        N = base * u
        lo = isqrt(2 * N) + 1
        D = rand_coprime(rng, lo, 50 * lo, N)
        B = Fr(N, D * D)
        if admissible(B):
            return B


def gen_manybeta(rng):
    """u = product of 6..10 distinct primes < 2000 (odd exponents), so beta has many primes."""
    plist = [int(p) for p in pari.primes(60) if int(p) > 13]
    while True:
        base = 1
        for p in S0:
            base *= p ** rng.randint(4, 5)
        u = 1
        for p in rng.sample(plist, rng.randint(6, 9)):
            u *= p
        N = base * u
        lo = isqrt(2 * N) + 1
        D = rand_coprime(rng, lo, 3 * lo, N)
        B = Fr(N, D * D)
        if admissible(B):
            return B


def gen_smooththeta(rng):
    """For m = 1 make theta a product of many small primes: N = D^2 - theta0 Y^2 with
    theta0 = 1 mod 8, a square mod 3, 5, 7, 13; Y chosen so that 2730^4 | N (2-part 2^4..)."""
    good_q = [int(q) for q in pari.primes(100) if int(q) > 13]
    while True:
        k = rng.randint(4, 9)
        qs = rng.sample(good_q, k)
        theta0 = 1
        for q in qs:
            theta0 *= q
        if theta0 % 8 != 1:
            continue
        if any(pow(theta0 % p, (p - 1) // 2, p) != 1 for p in (3, 5, 7, 13)):
            continue
        M = 2 ** 4 * 3 ** 4 * 5 ** 4 * 7 ** 4 * 13 ** 4
        D = rng.randrange(20 * M * isqrt(theta0), 200 * M * isqrt(theta0))
        if gcd(D, 2730 * theta0) != 1:
            continue
        # Y with theta0 Y^2 = D^2 mod M: Y = D / sqrt(theta0) mod M
        # sqrt of theta0 modulo each prime power, combined by CRT
        parts = []
        for p, e in [(2, 4), (3, 4), (5, 4), (7, 4), (13, 4)]:
            pe = p ** e
            if p != 2:
                r = int(pari(f"truncate(sqrt({theta0} + O({p}^{e})))")) % pe
            else:
                # theta0 = 1 mod 8: find r with r^2 = theta0 mod 2^5
                r = next(x for x in range(1, 2 ** 4, 2) if (x * x - theta0) % (2 ** 4) == 0)
            assert (r * r - theta0) % pe == 0
            parts.append((r, pe))
        sq = int(pari.chinese([pari.Mod(r, pe) for r, pe in parts]).lift())
        Y0 = (D * pow(sq, -1, M)) % M
        # need N = D^2 - theta0 Y^2 in (0, D^2/2): Y^2 in (D^2/(2 theta0), D^2/theta0)
        lo = isqrt(D * D // (2 * theta0)) + 1
        hi = isqrt(D * D // theta0)
        if hi - lo < 2 * M:
            continue
        Y = lo + ((Y0 - lo) % M) + M * rng.randrange(0, (hi - lo) // M - 1)
        N = D * D - theta0 * Y * Y
        if N <= 0 or gcd(N, D) != 1:
            continue
        B = Fr(N, D * D)
        if admissible(B) and sqfQ(1 - B) == theta0:
            return B


def gen_edgeS0(rng):
    """Minimal S0 valuations e_p in {4, 5}, tiny cofactor u (so beta is small, often 1 for some m)."""
    while True:
        base = 1
        for p in S0:
            base *= p ** rng.choice([4, 5])
        u = rng.choice([1, 1, 1, 11, 17, 19, 23, 29, 31, 37, 41])
        N = base * u
        lo = isqrt(2 * N) + 1
        D = rand_coprime(rng, lo, 4 * lo, N)
        B = Fr(N, D * D)
        if admissible(B):
            return B


def gen_extremeB(rng):
    """B very close to 1/2 (D^2 just above 2N) or B tiny (D huge)."""
    while True:
        base = 1
        for p in S0:
            base *= p ** rng.randint(4, 6)
        u = rng.randrange(1, 10 ** 4)
        if gcd(u, 2730) != 1:
            continue
        N = base * u
        if rng.random() < 0.5:
            D = isqrt(2 * N) + 1
            while gcd(D, N) != 1:
                D += 1
        else:
            D = rand_coprime(rng, 10 ** 30, 10 ** 31, N)
        B = Fr(N, D * D)
        if admissible(B):
            return B


GENS = dict(random=gen_random, manybeta=gen_manybeta, smooththeta=gen_smooththeta,
            edgeS0=gen_edgeS0, extremeB=gen_extremeB)


def main():
    fam, count, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    maxk = int(sys.argv[4]) if len(sys.argv) > 4 else 2
    mode = sys.argv[5] if len(sys.argv) > 5 else "first"
    auxb = 200
    rng = random.Random(seed)
    stats = dict(ok=0, fail=0)
    order = sorted(DIVS, key=lambda m: (m < 0, abs(m)))
    for i in range(count):
        B = GENS[fam](rng)
        t0 = time.time()
        info = f"#{i} num {len(str(Fr(B).numerator))}dig den {len(str(Fr(B).denominator))}dig " \
               f"omega(beta_1)={len(factor(sqfQ(B)))} omega(theta_1)={len(factor(sqfQ(1 - B)))} "
        if mode == "first":
            sol, tried = None, 0
            for k in range(0, maxk + 1):
                for m in order:
                    tried += 1
                    r = search_m(B, m, k, auxb)
                    if r:
                        sol = r
                        break
                if sol:
                    break
            dt = time.time() - t0
            if sol:
                stats["ok"] += 1
                print(info + f"OK m={sol['m']} k={sol['k']} n'={sol.get('nprime', '-')} "
                      f"kind={sol['kind']} omega(beta)={len(factor(sol['beta']))} "
                      f"omega(theta)={len(factor(sol['theta']))} (m,k) pairs tried={tried} ({dt:.1f}s)",
                      flush=True)
            else:
                stats["fail"] += 1
                print(info + f"FAIL B={B} ({dt:.1f}s)", flush=True)
        else:
            # stress mode: fixed multipliers, shortcuts n' = 1 and n' = theta forbidden
            ms = [m for m in order if m > 0][:6]
            res = []
            for m in ms:
                r = search_m_big(B, m) if mode == "stress" else search_m_random(B, m, rng)
                if r is None:
                    res.append(f"m={m}:FAIL[B={B}]")
                    stats["fail"] += 1
                else:
                    res.append(f"m={m}:" + ("th1" if r["kind"] == "theta=1" else f"k{r['k']}n'{r['nprime']}"))
                    stats["ok"] += 1
            print(info + " ".join(res) + f" ({time.time() - t0:.1f}s)", flush=True)
    print(fam, mode, stats)


if __name__ == "__main__":
    main()
