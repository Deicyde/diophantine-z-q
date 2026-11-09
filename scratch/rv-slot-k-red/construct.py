"""The slot construction of slot-k section 2.4, implemented from the text only.

construct(B, m, p0_choice, rng) -> dict with beta, theta, P, T, q0, R_P, R_T, n, and the
certification of C_|n| and C_|n|theta by the definition-based descent sel2.py.
Every prescribed choice is checked; if a choice is impossible the step is reported."""
from fractions import Fraction as Fr
import random
import gmpy2
import cypari2
from sel2 import leg, selmer_primes, in_pi1

pari = cypari2.Pari()
pari.allocatemem(2 * 10**9, silent=True) if hasattr(pari, 'allocatemem') else None

POS = [1, 2, 3, 5, 6, 7, 10, 13, 14, 15, 21, 26, 30, 35, 39, 42, 65, 70, 78, 91, 105, 130, 182,
       195, 210, 273, 390, 455, 546, 910, 1365, 2730]
DIVS = [s * a for a in POS for s in (1, -1)]
S0 = (2, 3, 5, 7, 13)


def factor(n):
    """dict prime->exponent of |n| (n != 0)."""
    n = abs(int(n))
    if n == 1:
        return {}
    F = pari.factor(n)
    return {int(F[0][i]): int(F[1][i]) for i in range(len(F[0]))}


def sqf_rat(r, known=None):
    """signed squarefree part of a nonzero rational and its prime set."""
    r = Fr(r)
    f = factor(r.numerator)
    for p, e in factor(r.denominator).items():
        f[p] = f.get(p, 0) + e
    s = -1 if r < 0 else 1
    val = s
    primes = []
    for p, e in f.items():
        if e % 2:
            val *= p; primes.append(p)
    return val, sorted(primes)


def v_p_rat(r, p):
    r = Fr(r)
    def vp(n):
        n = abs(n); k = 0
        while n % p == 0:
            n //= p; k += 1
        return k
    return vp(r.numerator) - vp(r.denominator)


def admissible(B):
    B = Fr(B)
    if not (0 < B < Fr(1, 2)):
        return False
    if gmpy2.is_square(B.denominator) is False:
        return False
    return all(v_p_rat(B, p) >= 4 for p in S0)


def lam(p): return 1 if p % 4 == 3 else 0


def eligible(B):
    out = []
    for m in DIVS:
        b, _ = sqf_rat(m * Fr(B))
        if b % 2 and abs(b) % 8 == 7:
            out.append(m)
    return out


def input_props(beta, P, theta, T):
    """(theta1)-(theta4) of slot-k 1.1; returns list of violated items."""
    bad = []
    if not (theta > 0 and theta % 8 == 1 and all(theta % p for p in S0)):
        bad.append('theta1')
    if set(P) & set(T):
        bad.append('theta2')
    if any(leg(beta, l) != 0 for l in T):
        bad.append('theta3')
    if any(leg(theta, p) != 0 for p in P if p != 2):
        bad.append('theta4')
    return bad


def residue_with_symbol(y, want, rng):
    """a residue r mod odd prime y, r != 0, with [r/y] = want."""
    while True:
        r = rng.randrange(1, y)
        if leg(r, y) == want:
            return r


def crt(congs):
    """congs: list of (residue, modulus) with pairwise coprime moduli."""
    a, M = 0, 1
    for r, m in congs:
        # solve x = a mod M, x = r mod m
        t = ((r - a) * pow(M, -1, m)) % m
        a, M = a + M * t, M * m
    return a % M, M


def find_prime(congs, extra, forbidden, rng, max_tries=10**7):
    """smallest-ish prime in the CRT progression satisfying extra symbol conditions
    extra: list of (y, want) meaning [prime/y] = want (y odd prime)."""
    a, M = crt(congs)
    k = rng.randrange(0, 10**6)
    for t in range(max_tries):
        c = a + M * (k + t)
        ok = True
        for y, want in extra:
            j = gmpy2.jacobi(c % y, y)
            if j == 0 or (0 if j == 1 else 1) != want:
                ok = False; break
        if not ok:
            continue
        if c in forbidden:
            continue
        if gmpy2.is_prime(c, 30):
            return c
    raise RuntimeError("no prime found")


VARIANT = None  # negative controls: 'wrongx', 'q0T', 'q0p'


def construct(B, m, rng, p0_choice='min'):
    B = Fr(B)
    beta, P = sqf_rat(m * B)
    theta, T = sqf_rat(m * (m - B))
    rec = dict(B=B, m=m, beta=beta, theta=theta, P=P, T=T)
    # Step 0 requirements
    if beta % 2 == 0 or abs(beta) % 8 != 7:
        rec['fail'] = 'step0: beta not odd with |beta| = 7 mod 8'
        return rec
    rec['inprops_bad'] = input_props(beta, P, theta, T)
    if p0_choice == 'min':
        p0 = min(P)
    elif p0_choice == 'max':
        p0 = max(P)
    elif isinstance(p0_choice, int):
        p0 = P[p0_choice % len(P)]
    else:
        p0 = rng.choice(P)
    rec['p0'] = p0
    s = 1 if beta < 0 else 0
    x = (s + 1) % 2
    if VARIANT == 'wrongx':
        x = s
    used = set(P) | set(T)
    # slot q0
    congs = [(3, 8)]
    tot = 0
    for p in P:
        if p == p0:
            continue
        want = (1 + lam(p) * x) % 2
        if VARIANT == 'q0p':
            want ^= 1
        tot ^= want
        congs.append((residue_with_symbol(p, want, rng), p))
    congs.append((residue_with_symbol(p0, (x + tot) % 2, rng), p0))
    for l in T:
        congs.append((residue_with_symbol(l, rng.randint(0, 1) if VARIANT == 'q0T' else 0, rng), l))
    q0 = find_prime(congs, [], used, rng)
    used.add(q0)
    assert sum(leg(q0, p) for p in P) % 2 == x
    rec['xbit'] = x
    # slots r_p
    RP = {}
    for p in P:
        if p == p0:
            continue
        congs = [(1, 8), (residue_with_symbol(p, 1, rng), p), (residue_with_symbol(p0, 1, rng), p0)]
        for y in P:
            if y not in (p, p0):
                congs.append((residue_with_symbol(y, 0, rng), y))
        for y in T:
            congs.append((residue_with_symbol(y, 0, rng), y))
        congs.append((residue_with_symbol(q0, 0, rng), q0))
        extra = [(r, 0) for r in RP.values()]
        r = find_prime(congs, extra, used, rng)
        RP[p] = r; used.add(r)
    # slots r_l
    RT = {}
    for l in T:
        congs = [(1, 8), (residue_with_symbol(l, 1, rng), l), (residue_with_symbol(q0, 1, rng), q0)]
        for y in P:
            congs.append((residue_with_symbol(y, 0, rng), y))
        for y in T:
            if y != l:
                congs.append((residue_with_symbol(y, 0, rng), y))
        extra = [(r, 0) for r in RP.values()] + [(r, 0) for r in RT.values()]
        r = find_prime(congs, extra, used, rng)
        RT[l] = r; used.add(r)
    n = beta * q0
    for r in RP.values():
        n *= r
    for r in RT.values():
        n *= r
    rec.update(q0=q0, RP=RP, RT=RT, n=n, slots=1 + len(RP) + len(RT))
    # certification by the definition-based descent
    d1p = sorted(P + [q0] + list(RP.values()) + list(RT.values()))
    d1 = abs(n)
    d2p = sorted(d1p + T)
    d2 = d1 * theta
    res = []
    for d, ps in ((d1, d1p), (d2, d2p)):
        dim, ker, gens = selmer_primes(d, ps)
        res.append((dim, in_pi1(beta, ker, gens), d % 8))
    rec['cert'] = res
    rec['ok'] = all(dim == 3 and inn for dim, inn, _ in res)
    return rec


def summary(rec):
    if 'fail' in rec:
        return "m=%d FAIL %s" % (rec['m'], rec['fail'])
    c = rec['cert']
    return ("m=%6d beta=%s|%d| w(b)=%d w(t)=%d P=%s T=%s p0=%d slots=%d d1:(dim %d, beta %s, %d) "
            "d2:(dim %d, beta %s, %d) inprops_bad=%s %s" % (
                rec['m'], '-' if rec['beta'] < 0 else '+', abs(rec['beta']) % 8, len(rec['P']),
                len(rec['T']), [p % 8 for p in rec['P']] if len(rec['P']) < 8 else '...',
                [l % 8 for l in rec['T']] if len(rec['T']) < 8 else '...', rec['p0'] % 8 if rec['p0'] > 13 else rec['p0'],
                rec['slots'], c[0][0], c[0][1], c[0][2], c[1][0], c[1][1], c[1][2],
                rec['inprops_bad'], 'OK' if rec['ok'] else '*** FAILURE ***'))
