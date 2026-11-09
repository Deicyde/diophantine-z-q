"""Own implementation of the slot construction of slot-k section 2.4, from the text only.

build(B, m, rng, wrong_x=False) returns a dict with beta, theta, P, T, q0, R_P, R_T, n.
The prime search imposes the conditions modulo 8 and modulo the primes of beta*theta by CRT,
and the conditions modulo earlier slots by testing (gmpy2 Legendre symbols)."""
from fractions import Fraction as Fr
from math import gcd, isqrt, prod

import cypari2
import gmpy2

pari = cypari2.Pari()
pari.allocatemem(2 * 10 ** 9)

S0 = [2, 3, 5, 7, 13]
POS = [a for a in range(1, 2731) if 2730 % a == 0]
DIVS = [s * a for a in POS for s in (1, -1)]


def factor(n):
    n = abs(int(n))
    if n <= 1:
        return {}
    f = pari.factor(n)
    return {int(p): int(e) for p, e in zip(f[0], f[1])}


def sqf_int(n):
    out = -1 if n < 0 else 1
    for p, e in factor(n).items():
        if e % 2:
            out *= p
    return out


def vpQ(r, p):
    def v(n):
        n = abs(n); k = 0
        while n % p == 0:
            n //= p; k += 1
        return k
    return v(r.numerator) - v(r.denominator)


def admissible(B):
    D = B.denominator
    return isqrt(D) ** 2 == D and 0 < B < Fr(1, 2) and all(vpQ(B, p) >= 4 for p in S0)


def bit(y, p):
    """[y/p] for odd prime p, y prime to p."""
    l = gmpy2.legendre(y % p, p)
    assert l != 0
    return 0 if l == 1 else 1


def beta_theta(B, m):
    beta = sqf_int((m * B).numerator * (m * B).denominator)
    t = m * (m - B)
    theta = sqf_int(t.numerator * t.denominator)
    return beta, theta


def eligible(B):
    out = []
    for m in DIVS:
        beta, theta = beta_theta(B, m)
        if beta % 2 and abs(beta) % 8 == 7:
            out.append(m)
    return out


def check_theta(beta, theta):
    """(theta1)-(theta4), checked directly."""
    P = sorted(factor(beta)); T = sorted(factor(theta))
    t1 = theta > 0 and theta % 8 == 1 and gcd(theta, 2730) == 1
    t2 = not (set(P) & set(T))
    t3 = all(bit(beta, l) == 0 for l in T)
    t4 = all(bit(theta, p) == 0 for p in P if p != 2)
    return t1, t2, t3, t4


def residue_with(p, b, rng):
    """A residue r mod p, r != 0, with [r/p] = b."""
    while True:
        r = rng.randrange(1, p)
        if bit(r, p) == b:
            return r


def find_prime(c8, crt_conds, test_conds, used, rng):
    """Prime r = c8 (mod 8), [r/y] = b for (y, b) in crt_conds (imposed by CRT) and in test_conds
    (imposed by search), r not in used."""
    mods = [8] + [y for y, _ in crt_conds]
    ress = [c8] + [residue_with(y, b, rng) for y, b in crt_conds]
    r0 = int(pari.lift(pari.chinese([pari.Mod(a, q) for a, q in zip(ress, mods)])))
    M = prod(mods)
    k = rng.randrange(1, 1000)
    while True:
        r = r0 + k * M
        k += 1
        if r in used:
            continue
        if all(gmpy2.legendre(r % y, y) == (1 if b == 0 else -1) for y, b in test_conds):
            if gmpy2.is_prime(r, 30):
                return r


def build(B, m, rng, wrong_x=False):
    beta, theta = beta_theta(B, m)
    assert beta % 2 and abs(beta) % 8 == 7
    P = sorted(factor(beta)); T = sorted(factor(theta))
    lam = lambda p: 1 if p % 4 == 3 else 0
    p0 = P[0]
    s = 1 if beta < 0 else 0
    x = s if wrong_x else (s + 1) % 2
    used = set(P) | set(T)
    # slot q0
    conds = [(p, (1 + lam(p) * x) % 2) for p in P if p != p0]
    conds.append((p0, (x + sum(b for _, b in conds)) % 2))
    conds += [(l, 0) for l in T]
    q0 = find_prime(3, conds, [], used, rng)
    used.add(q0)
    # slots r_p
    RP = {}
    for p in P:
        if p == p0:
            continue
        crt = [(p, 1), (p0, 1)] + [(y, 0) for y in P if y not in (p, p0)] + [(l, 0) for l in T]
        test = [(q0, 0)] + [(r, 0) for r in RP.values()]
        r = find_prime(1, crt, test, used, rng)
        RP[p] = r; used.add(r)
    # slots r_l
    RT = {}
    for l in T:
        crt = [(l, 1)] + [(y, 0) for y in P] + [(y, 0) for y in T if y != l]
        test = [(q0, 1)] + [(r, 0) for r in RP.values()] + [(r, 0) for r in RT.values()]
        r = find_prime(1, crt, test, used, rng)
        RT[l] = r; used.add(r)
    n = beta * q0 * prod(RP.values()) * prod(RT.values())
    return dict(beta=beta, theta=theta, P=P, T=T, p0=p0, s=s, x=x, q0=q0, RP=RP, RT=RT, n=n)
