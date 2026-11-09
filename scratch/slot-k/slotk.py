"""The slot construction of docs/research/slot-k.md with actual primes.

Input: admissible B.  Output: (m, beta, theta, q0, R_P, R_T, n) with n = beta*q0*prod(R_P)*prod(R_T).
Primes are produced by CRT + a primality search in the prescribed residue class."""
import os, sys
from fractions import Fraction as Fr
from math import prod
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "rv-route-k"))
from sel2cong import selmer, vec_of, first_coord_contains  # exact 2-descent (no PARI needed)

S0 = [2, 3, 5, 7, 13]
POS = [1, 2, 3, 5, 6, 7, 10, 13, 14, 15, 21, 26, 30, 35, 39, 42, 65, 70, 78, 91, 105, 130, 182,
       195, 210, 273, 390, 455, 546, 910, 1365, 2730]
DIVS = sorted({s * a for a in POS for s in (1, -1)}, key=lambda m: (m < 0, abs(m)))


def is_prime(n):
    if n < 2: return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0: return n == p
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41):
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else:
            return False
    return True


def leg(a, p):
    a %= p
    return 0 if pow(a, (p - 1) // 2, p) == 1 else 1


def nonres(p):
    g = 2
    while leg(g, p) == 0: g += 1
    return g


def prime_with(cls8, symbols, avoid):
    """A prime q = cls8 (mod 8) with [q/p] = symbols[p] for each odd prime p, q not in avoid."""
    a, M = cls8 % 8, 8
    for p, e in symbols.items():
        r = 1 if e == 0 else nonres(p)
        # CRT: x = a mod M, x = r mod p
        t = ((r - a) * pow(M, -1, p)) % p
        a, M = a + M * t, M * p
    q = a
    while True:
        if q not in avoid and q > 2 and is_prime(q):
            return q
        q += M


def factor_small(n, primes_hint=()):
    """Factor |n| using trial division by hints and a PARI-free Pollard rho."""
    n = abs(n); out = {}
    for p in primes_hint:
        while n % p == 0: out[p] = out.get(p, 0) + 1; n //= p
    stack = [n] if n > 1 else []
    import random
    while stack:
        x = stack.pop()
        if x == 1: continue
        if is_prime(x): out[x] = out.get(x, 0) + 1; continue
        f = None
        for p in range(2, 10000):
            if x % p == 0: f = p; break
        if f is None:
            from math import gcd
            while True:
                c = random.randrange(1, x); y = random.randrange(x); z = y; g = 1
                while g == 1:
                    y = (y * y + c) % x; z = (z * z + c) % x; z = (z * z + c) % x
                    g = gcd(abs(y - z), x)
                if g != x: f = g; break
        stack += [f, x // f]
    return out


def sqf(r, fac):
    r = Fr(r)
    sgn = -1 if r < 0 else 1
    fn, fd = fac(r.numerator), fac(r.denominator)
    out = sgn
    for p in set(fn) | set(fd):
        if (fn.get(p, 0) + fd.get(p, 0)) % 2: out *= p
    return out


def choose_m(B, fac):
    """Signed divisors m of 2730 with beta = sqf(mB) odd and |beta| = 7 (mod 8)."""
    res = []
    for m in DIVS:
        beta = sqf(m * B, fac)
        if beta % 2 and abs(beta) % 8 == 7:
            res.append(m)
    return res


def construct(beta, theta, P, T):
    """The slots.  P, T: odd primes of beta, theta."""
    s = 1 if beta < 0 else 0
    x = (s + 1) % 2
    lam = {p: (p % 4 == 3) * 1 for p in P}
    p0, Prest = P[0], P[1:]
    sym = {p: (1 + lam[p] * x) % 2 for p in Prest}
    sym[p0] = (x + sum(sym.values())) % 2
    for l in T: sym[l] = 0
    used = set(P) | set(T)
    q0 = prime_with(3, sym, used); used.add(q0)
    RP = []
    for p in Prest:
        sy = {y: 0 for y in P + T + [q0] + RP}
        sy[p] = 1; sy[p0] = 1
        r = prime_with(1, sy, used); used.add(r); RP.append(r)
    RT = []
    for l in T:
        sy = {y: 0 for y in P + T + [q0] + RP + RT}
        sy[l] = 1; sy[q0] = 1
        r = prime_with(1, sy, used); used.add(r); RT.append(r)
    return q0, RP, RT


def certified(d, dprimes, beta):
    """'torsion', 'selmer3', or None (exact 2-descent of sel2cong)."""
    from math import isqrt
    t = abs(beta * d)
    # beta*d a square up to sign?
    g = 1
    if isqrt(t) ** 2 == t: return "torsion"
    basis, gens = selmer(d, sorted(dprimes))
    if len(basis) == 3 and first_coord_contains(basis, vec_of(beta, gens)):
        return "selmer3"
    return ("dim", len(basis))
