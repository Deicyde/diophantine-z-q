"""DL end to end with actual primes, certified by the own exact descent sel2.py.

Own implementation of the construction of slot-k §2.4 (not importing scratch/slot-k). PARI
(cypari2) is used only to factor integers and to test primality (BPSW). 30 runs (B, m), sequential.
Families: random admissible B; theta = 1 (both signs of beta); beta with only primes = 3 mod 4;
prescribed theta with many primes, including primes = 3 mod 4, with beta of either sign.
"""
import random
import sys
from fractions import Fraction
from math import gcd, isqrt
import cypari2
from sel2 import selmer, has_first_coord, legendre_bit

pari = cypari2.Pari()
pari.allocatemem(2 * 10 ** 9)
S0 = [2, 3, 5, 7, 13]
DIVS = []
for mask in range(32):
    v = 1
    for i, p in enumerate([2, 3, 5, 7, 13]):
        if mask >> i & 1:
            v *= p
    DIVS += [v, -v]


def isprime(n):
    return bool(pari.ispseudoprime(n))  # BPSW


def factor(n):
    n = abs(n)
    if n == 1:
        return {}
    f = pari.factor(n)
    return {int(f[0][i]): int(f[1][i]) for i in range(len(f[0]))}


def sqf(r):
    """Signed squarefree part of a nonzero rational, with its primes."""
    r = Fraction(r)
    den = r.denominator
    fs = factor(r.numerator)
    if isqrt(den) ** 2 != den:  # a square denominator does not change the square class
        for p, e in factor(den).items():
            fs[p] = fs.get(p, 0) + e
    ps = sorted(p for p, e in fs.items() if e % 2)
    v = -1 if r < 0 else 1
    for p in ps:
        v *= p
    return v, ps


def vp(r, p):
    r = Fraction(r)
    k = 0
    a, b = r.numerator, r.denominator
    while a % p == 0:
        a //= p
        k += 1
    while b % p == 0:
        b //= p
        k -= 1
    return k


def admissible(B):
    if not (0 < B < Fraction(1, 2)):
        return False
    d = B.denominator
    if isqrt(d) ** 2 != d:
        return False
    return all(vp(B, p) >= 4 for p in S0)


def eligible_ms(B):
    out = []
    for m in DIVS:
        beta, P = sqf(m * B)
        if beta % 2 and abs(beta) % 8 == 7:
            out.append(m)
    return out


def jac_bit(a, p):
    return legendre_bit(a, p)


def find_prime(rng, cls8, conds, avoid, base):
    """Prime r = cls8 mod 8, with [r/y] = bit for (y, bit) in conds, r not in avoid.

    CRT over the moduli in `base` (the primes of beta and theta; residues chosen at random with
    the required symbol), then search the progression testing the conditions at earlier slots.
    Keeping earlier slots out of the CRT modulus keeps the slots from doubling in size.
    """
    crt = [cy for cy in conds if cy[0] in base]
    rest = [cy for cy in conds if cy[0] not in base]
    M = 8
    a = cls8
    for y, bit in crt:
        while True:
            t = rng.randrange(1, y)
            if jac_bit(t, y) == bit:
                break
        # combine a mod M with t mod y
        k = ((t - a) * pow(M, -1, y)) % y
        a = a + M * k
        M *= y
    start = rng.randrange(0, 10 ** 6)
    j = start
    while True:
        r = a + M * j
        j += 1
        if r in avoid or r < 3:
            continue
        if any(jac_bit(r, y) != bit for y, bit in rest):
            continue
        if not isprime(r):
            continue
        assert r % 8 == cls8 and all(jac_bit(r, y) == bit for y, bit in conds)
        return r


def lam(p):
    return 1 if p % 4 == 3 else 0


def construct(rng, beta, P, T):
    s = 1 if beta < 0 else 0
    x = (s + 1) % 2
    p0, rest = P[0], P[1:]
    used = set(P) | set(T)
    base = set(P) | set(T)
    conds = []
    tot = 0
    for p in rest:
        b = (1 + lam(p) * x) % 2
        conds.append((p, b))
        tot ^= b
    conds.append((p0, x ^ tot))
    conds += [(l, 0) for l in T]
    q0 = find_prime(rng, 3, conds, used, base)
    used.add(q0)
    RP = []
    for p in rest:
        conds = [(p, 1), (p0, 1)] + [(y, 0) for y in rest if y != p] + [(l, 0) for l in T] \
            + [(q0, 0)] + [(r, 0) for r in RP]
        r = find_prime(rng, 1, conds, used, base)
        used.add(r)
        RP.append(r)
    RT = []
    for l in T:
        conds = [(l, 1), (q0, 1)] + [(p, 0) for p in P] + [(y, 0) for y in T if y != l] \
            + [(r, 0) for r in RP] + [(r, 0) for r in RT]
        r = find_prime(rng, 1, conds, used, base)
        used.add(r)
        RT.append(r)
    return q0, RP, RT


def certify(d, primes, beta):
    dim, ker, gens = selmer(d, sorted(primes))
    return dim, has_first_coord(ker, gens, beta)


# ---------------- input families ----------------
def rand_primes(rng, k, lo, hi, cond=lambda p: True):
    out = set()
    while len(out) < k:
        p = rng.randrange(lo, hi)
        if p not in S0 and cond(p) and isprime(p):
            out.add(p)
    return sorted(out)


def fam_random(rng):
    while True:
        kprimes = rand_primes(rng, rng.randint(1, 6), 11, 2000)
        k = 1
        for p in kprimes:
            k *= p
        D = rng.randrange(10 ** 8, 10 ** 9) * isqrt(k) + rng.randrange(1, 10 ** 6)
        if gcd(D, 2730 * k) != 1:
            continue
        B = Fraction(2730 ** 4 * k * rng.choice([1, 2, 3, 6, 10, 21]), D * D)
        if admissible(B):
            ms = eligible_ms(B)
            if ms:
                return B, rng.choice(ms)


def fam_theta1(rng, sign):
    """B = m(1 - c^2) with c = u/w, theta = 1 for this m; m = sign * (odd divisor)."""
    while True:
        m = sign * rng.choice([1, 3, 5, 7, 15, 21, 35, 105])
        if sign > 0:
            # 1 - c^2 > 0 small: u = w - 2730^4 j (j odd so v2 stays controlled)
            w = rng.randrange(10 ** 17, 10 ** 18) * m * 8 + 1
            u = w - 2730 ** 4 * rng.randrange(1, 50)
        else:
            w = rng.randrange(10 ** 17, 10 ** 18) * abs(m) * 8 + 1
            u = w + 2730 ** 4 * rng.randrange(1, 50)
        if gcd(u, w) != 1 or gcd(w, 2730) != 1:
            continue
        B = m * Fraction(w * w - u * u, w * w)
        if not admissible(B):
            continue
        beta, P = sqf(m * B)
        theta, T = sqf(m * (m - B))
        if theta == 1 and beta % 2 and abs(beta) % 8 == 7:
            return B, m


def fam_beta3mod4(rng):
    """B = 2730^4 k / D^2, k a product of primes = 3 mod 4, m in {1,-1,3,-3,7,-7,21,-21}."""
    while True:
        kprimes = rand_primes(rng, rng.choice([1, 3, 5]), 11, 3000, lambda p: p % 4 == 3)
        k = 1
        for p in kprimes:
            k *= p
        D = rng.randrange(10 ** 9, 10 ** 10) * isqrt(k) + rng.randrange(1, 10 ** 6)
        if gcd(D, 2730 * k) != 1:
            continue
        B = Fraction(2730 ** 4 * k, D * D)
        if not admissible(B):
            continue
        ms = [m for m in eligible_ms(B) if abs(m) in (1, 3, 7, 21)]
        if ms:
            m = rng.choice(ms)
            beta, P = sqf(m * B)
            assert all(p % 4 == 3 for p in P)
            return B, m


def fam_theta(rng, nT, sign):
    """Prescribed theta (nT primes, at least one = 3 mod 4), B = m(1 - theta c^2)."""
    while True:
        T = rand_primes(rng, nT, 11, 400)
        theta = 1
        for p in T:
            theta *= p
        if theta % 8 != 1 or not any(p % 4 == 3 for p in T):
            continue
        # theta must be a square mod 3, 5, 7, 13 (theta = 1 mod 8 is a 2-adic square)
        if any(legendre_bit(theta, p) for p in [3, 5, 7, 13]):
            continue
        break
    while True:
        m = sign * rng.choice([1, 3, 5, 7, 15, 21, 35, 105])
        # want theta u^2 = w^2 mod N, N = 2^7 3^4 5^4 7^4 13^4; take u = 1 mod N-part, w = sqrt(theta)
        N = 2 ** 7 * 3 ** 4 * 5 ** 4 * 7 ** 4 * 13 ** 4
        # w0 with w0^2 = theta mod N (CRT of Hensel lifts)
        w0 = 0
        Mo = 1
        for p, k in [(2, 7), (3, 4), (5, 4), (7, 4), (13, 4)]:
            q = p ** k
            r = next(t for t in range(1, q) if (t * t - theta) % q == 0)
            k2 = ((r - w0) * pow(Mo, -1, q)) % q
            w0 += Mo * k2
            Mo *= q
        # u = 1 + N*j, w = w0 + N*i with w^2 - theta u^2 small positive (sign>0) or negative
        u = 1 + N * rng.randrange(10 ** 10, 10 ** 11)
        target = isqrt(theta * u * u)
        w = target - (target - w0) % N
        if sign > 0:
            w += N * rng.randrange(1, 5)  # w^2 > theta u^2
        else:
            w -= N * rng.randrange(0, 5)  # w^2 < theta u^2
        if gcd(w, 2730 * theta * u) != 1:
            continue
        B = m * Fraction(w * w - theta * u * u, w * w)
        if not admissible(B):
            continue
        th, TT = sqf(m * (m - B))
        if th != theta:
            continue
        beta, P = sqf(m * B)
        if beta % 2 and abs(beta) % 8 == 7:
            return B, m


def run(B, m, rng, label):
    beta, P = sqf(m * B)
    theta, T = sqf(m * (m - B))
    assert theta > 0 and theta % 8 == 1 and gcd(theta, 2730) == 1 and not set(P) & set(T)
    assert all(legendre_bit(beta, l) == 0 for l in T)  # (θ3)
    assert all(legendre_bit(theta, p) == 0 for p in P)  # (θ4)
    q0, RP, RT = construct(rng, beta, P, T)
    aux = [q0] + RP + RT
    n = abs(beta)
    for r in aux:
        n *= r
    c1 = certify(n, P + aux, beta)
    c2 = certify(n * theta, P + aux + T, beta)
    ok = c1 == (3, True) and c2 == (3, True)
    nlam = sum(lam(l) for l in T)
    print("%-10s m=%5d beta<0=%d w(beta)=%2d w(theta)=%2d (=3mod4: %d) slots=%2d maxdigits=%3d "
          "C_n=%s C_ntheta=%s %s" % (label, m, beta < 0, len(P), len(T), nlam, len(aux),
                                     max(len(str(a)) for a in aux), c1, c2,
                                     "OK" if ok else "FAIL"), flush=True)
    return ok


if __name__ == "__main__":
    rng = random.Random(20261108)
    plan = [('random', None)] * 12 + [('theta1+', None)] * 3 + [('theta1-', None)] * 3 + \
           [('beta3mod4', None)] * 5 + [('theta+', None)] * 4 + [('theta-', None)] * 3
    good = 0
    for fam, _ in plan:
        if fam == 'random':
            B, m = fam_random(rng)
        elif fam == 'theta1+':
            B, m = fam_theta1(rng, 1)
        elif fam == 'theta1-':
            B, m = fam_theta1(rng, -1)
        elif fam == 'beta3mod4':
            B, m = fam_beta3mod4(rng)
        elif fam == 'theta+':
            B, m = fam_theta(rng, rng.randint(3, 6), 1)
        else:
            B, m = fam_theta(rng, rng.randint(3, 6), -1)
        good += run(B, m, rng, fam)
    print("runs:", len(plan), "both curves certified:", good)
