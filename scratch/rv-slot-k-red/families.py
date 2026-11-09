"""Adversarial input families; each returns a list of (B, m, p0_choice, tag), at most 30."""
from fractions import Fraction as Fr
from gens import *
from construct import eligible, sqf_rat


def random30(rng):
    out = []
    for i in range(30):
        B = gen_random(rng)
        m = rng.choice(eligible(B))
        out.append((B, m, 'rand', 'random'))
    return out


def smoke(rng):
    return random30(rng)[:5]


def primes_cls(rng, cls, k, lo=17, hi=10**4, mod=8, avoid=()):
    out = []
    while len(out) < k:
        p = rand_prime(rng, lo, hi, cls, mod)
        if p not in out and p not in avoid:
            out.append(p)
    return out


def prod(xs):
    r = 1
    for x in xs:
        r *= x
    return r


def beta_with_classes(rng, classes, sign=None, lo=17, hi=10**4):
    """odd squarefree beta whose primes have the given classes mod 8 (product must be 7)."""
    ps = []
    for c in classes:
        ps += primes_cls(rng, c, 1, lo, hi, avoid=ps)
    b = prod(ps)
    assert b % 8 == 7, (classes, b % 8)
    sg = rng.choice([1, -1]) if sign is None else sign
    return sg * b


def theta1(rng):
    """theta = 1 for the designed multiplier; omega(beta) = 1..4, both signs, P inside and
    outside S0."""
    betas = [7, -7, 15, -15, 39, -39, 455, -455]
    for c in ([7], [7], [3, 5], [1, 7], [3, 3, 7], [5, 5, 7], [1, 1, 7], [3, 7, 7, 3],
              [3, 1, 5, 1], [7, 7, 7], [3], [5, 3], [1, 3, 5], [5, 7, 5], [1, 1, 1, 7]):
        if prod(c) % 8 == 7:
            betas.append(beta_with_classes(rng, c))
    out = []
    for b in betas:
        B, m = gen_theta_one(rng, b)
        if B is not None:
            out.append((B, m, 'rand', 'theta1 b=%d' % b if abs(b) < 1000 else 'theta1'))
    return out[:30]


def omega1(rng):
    """omega(beta) = 1: beta = +-p, p = 7 mod 8 (p = 7 or large); theta with primes in each class."""
    out = []
    ps = [7, 23, 31, 47, 71, 10007 * 0 + 10079, 999983]
    ps = [p for p in ps if p % 8 == 7 and gmpy2.is_prime(p)] + [rand_prime(rng, 10**6, 10**8, 7)]
    wants = [None,
             lambda th, T: any(l % 8 == 3 for l in T),
             lambda th, T: any(l % 8 == 5 for l in T),
             lambda th, T: any(l % 8 == 7 for l in T),
             lambda th, T: len(T) == 1]
    for p in ps:
        for sg in (1, -1):
            w = rng.choice(wants)
            B, m = gen_from_beta(rng, sg * p, want=w)
            if B is not None:
                out.append((B, m, 'min', 'omega1 b=%d' % (sg * p)))
    return out[:30]


def all3mod4(rng):
    """every prime of beta = 3 mod 4 (classes 3, 7), both signs, omega 1..7."""
    out = []
    for c in ([7], [3, 3, 7], [3, 7, 7, 3, 7], [7, 7, 7], [3, 3, 3, 3, 7], [7, 7, 3, 3, 7, 7, 7],
              [3, 7, 3, 7, 3, 3, 7]):
        assert prod(c) % 8 == 7
        for sg in (1, -1):
            b = beta_with_classes(rng, c, sg)
            for w in (None, lambda th, T: any(l % 4 == 3 for l in T)):
                B, m = gen_from_beta(rng, b, want=w)
                if B is not None:
                    out.append((B, m, 'rand', 'all3mod4 w=%d' % len(c)))
    return out[:30]


def mostly1mod4(rng):
    """beta = one prime = 3 mod 4 times primes = 1 mod 4 (classes 1, 5)."""
    out = []
    for c in ([7, 1], [7, 1, 1, 1], [3, 5], [3, 5, 1, 1], [7, 5, 5], [7, 5, 5, 5, 5],
              [3, 5, 5, 5], [7, 1, 5, 1, 5, 1, 1], [3, 1, 1, 1, 1, 5, 1]):
        assert prod(c) % 8 == 7, c
        for sg in (1, -1):
            b = beta_with_classes(rng, c, sg)
            B, m = gen_from_beta(rng, b, want=lambda th, T: len(T) >= 1)
            if B is not None:
                out.append((B, m, 'rand', 'mostly1mod4 w=%d' % len(c)))
    return out[:30]


def thetacls(rng):
    """theta with primes in prescribed classes mod 8 (3, 5, 7 each present, or only 3s, ...)."""
    out = []
    conds = [lambda th, T: {3, 5, 7} <= {l % 8 for l in T},
             lambda th, T: len(T) >= 2 and all(l % 8 == 3 for l in T),
             lambda th, T: len(T) >= 2 and all(l % 8 == 7 for l in T),
             lambda th, T: len(T) >= 2 and all(l % 8 == 5 for l in T),
             lambda th, T: len(T) >= 1 and all(l % 8 == 1 for l in T),
             lambda th, T: len(T) == 2 and all(l % 4 == 3 for l in T)]
    for i in range(30):
        c = rng.choice([[7], [3, 5], [7, 1, 3, 3], [5, 3, 1]])
        b = beta_with_classes(rng, c)
        k = i % len(conds)
        B, m = gen_from_beta(rng, b, want=conds[k], abound=300, tries=20000)
        if B is not None:
            out.append((B, m, 'rand', 'thetacls%d' % k))
    return out[:30]


def core_primes(rng, k, lo=2 * 10**4, hi=3 * 10**6):
    """k primes = 1 mod 21840, pairwise quadratic residues (an isotropic core, descent-alt Prop B)."""
    from sel2 import leg
    while True:
        K = []
        tries = 0
        while len(K) < k and tries < 20000:
            tries += 1
            p = rng.randrange(lo // 21840, hi // 21840) * 21840 + 1
            if p in K or not gmpy2.is_prime(p):
                continue
            if all(leg(p, q) == 0 for q in K):
                K.append(p)
        if len(K) == k:
            return K


def S0power(rng):
    return 2 ** rng.randint(4, 7) * 3 ** rng.randint(4, 7) * 5 ** rng.randint(4, 7) \
        * 7 ** rng.randint(4, 7) * 13 ** rng.randint(4, 7)


def B_over(rng, N):
    """admissible B = N / D^2 with D coprime to N, D^2 > 2N."""
    while True:
        D = int(gmpy2.isqrt(2 * N)) + rng.randrange(1, 10**6)
        if gmpy2.gcd(D, N) == 1:
            B = Fr(N, D * D)
            if admissible(B):
                return B


def cores(rng):
    """beta = (isotropic core of size k) x (S0 part from the multiplier); every eligible m."""
    out = []
    for k, nm in ((3, 8), (4, 8), (6, 8), (5, 6)):
        K = core_primes(rng, k)
        N = S0power(rng) * prod(K)
        B = B_over(rng, N)
        ms = eligible(B)
        rng.shuffle(ms)
        for m in ms[:nm]:
            out.append((B, m, 'rand', 'core%d' % k))
    return out[:30]


def cores_extra(rng):
    """core of size k plus one large prime = 7 mod 8 (or 3 mod 8) in B; theta via t."""
    out = []
    for i in range(30):
        k = rng.choice([3, 4, 5, 6])
        K = core_primes(rng, k)
        e = rand_prime(rng, 10**3, 10**7, rng.choice([3, 7]))
        b0 = prod(K) * e
        # pick S0-part so that |beta| = 7 mod 8
        for f in (1, 3, 5, 7, 15, 39, 455, 21, 35, 13):
            if (b0 * f) % 8 == 7:
                break
        b = rng.choice([1, -1]) * b0 * f
        B, m = gen_from_beta(rng, b)
        if B is not None:
            out.append((B, m, 'rand', 'core%d+e' % k))
    return out


def s0beta(rng):
    """P inside {3,5,7,13}: beta in +-{7, 15, 39, 455}, nontrivial theta, all p0 choices."""
    out = []
    for b in (7, -7, 15, -15, 39, -39, 455, -455):
        for j in range(4 if abs(b) == 455 else 3):
            B, m = gen_from_beta(rng, b, want=lambda th, T: len(T) >= 1)
            if B is not None:
                out.append((B, m, j, 's0beta %d' % b))
    return out[:30]


def allm(rng):
    """3 random inputs, every eligible multiplier (both signs, all odd parts = 7)."""
    out = []
    for i in range(3):
        B = gen_random(rng)
        for m in eligible(B):
            out.append((B, m, 'rand', 'allm%d' % i))
    return out[:30]


def p0var(rng):
    """one input per beta size, every choice of p0."""
    out = []
    for c in ([3, 5, 1, 1, 5, 3, 7], [7, 7, 7, 1, 5, 3, 5, 3]):
        b = beta_with_classes(rng, c) if prod(c) % 8 == 7 else None
        if b is None:
            continue
        B, m = gen_from_beta(rng, b, want=lambda th, T: len(T) >= 2)
        for j in range(len(c)):
            out.append((B, m, j, 'p0var'))
    return out[:30]


CONTACT = (0, 15, 20, 24, 30, 60)


def Fpoly(t):
    r = Fr(1)
    for c in CONTACT:
        r *= (t + c)
    return r


def slope_pattern_uv(rng, lo=10**3, hi=10**6, v=None):
    """t = u/v with every |u + c v| (c in the contact set) a prime = +-1 mod 8 (six good slope
    primes, as under 22P2): v = 0 mod 8, u = +-1 mod 8."""
    while True:
        vv = v if v is not None else 8 * rng.randint(1, 50)
        u = rng.randrange(lo, hi) * rng.choice([1, -1])
        if u % 8 not in (1, 7) or gmpy2.gcd(u, vv) != 1:
            continue
        if all(gmpy2.is_prime(abs(u + c * vv)) for c in CONTACT):
            return u, vv


def slope_site(rng):
    """slope call site: R0 = eta F(t)/(t-1)^8 with six good slope primes, B = R0 s^2."""
    out = []
    while len(out) < 30:
        u, v = slope_pattern_uv(rng)
        t = Fr(u, v)
        R0 = Fpoly(t) / (t - 1) ** 8
        eta = 1 if R0 > 0 else -1
        R0 *= eta
        for _ in range(200):
            s = Fr(2730 ** rng.randint(2, 4) * rng.randint(1, 30), rng.randrange(10**3, 10**12))
            B = R0 * s * s
            if admissible(B):
                break
        else:
            continue
        ms = eligible(B)
        m = rng.choice(ms)
        out.append((B, m, 'rand', 'slope u=%d v=%d' % (u, v)))
    return out


def test_site(rng):
    """test call site: R0 = eta 2730^6 F(n), n integer, B = R0 s^2 (s may have v_p = -1 on S0)."""
    out = []
    while len(out) < 30:
        n = rng.choice([rng.randint(-200, 200), rng.randint(-10**4, 10**4), rng.randint(-10**6, 10**6)])
        if n in (0, -15, -20, -24, -30, -60):
            continue
        R0 = 2730 ** 6 * Fpoly(Fr(n))
        eta = 1 if R0 > 0 else -1
        R0 *= eta
        bound = int(gmpy2.isqrt(int(R0))) * 2 + 2
        for _ in range(200):
            a = rng.randint(1, 50)
            s = Fr(a, 2730 * rng.randrange(bound // 2730 * a + 1, bound // 2730 * a * 4 + 10))
            B = R0 * s * s
            if admissible(B):
                break
        else:
            continue
        m = rng.choice(eligible(B))
        out.append((B, m, 'rand', 'test n=%d' % n))
    return out


def large(rng):
    """omega(beta) 9-12, theta with several primes (up to about 20 slots)."""
    out = []
    for i in range(12):
        k = rng.randint(9, 12)
        while True:
            cs = [rng.choice((1, 3, 5, 7)) for _ in range(k)]
            if prod(cs) % 8 == 7:
                break
        b = beta_with_classes(rng, cs, lo=17, hi=3000)
        B, m = gen_from_beta(rng, b, abound=5, want=lambda th, T: len(T) >= 3)
        if B is not None:
            out.append((B, m, 'rand', 'large w=%d' % k))
    return out


def small_slots(rng):
    """random inputs, slots taken as the least primes of their progressions (q0 may be 3, 11, ...)."""
    out = []
    for i in range(10):
        B = gen_random(rng, kmax=3)
        m = rng.choice(eligible(B))
        out.append((B, m, 'rand', 'small'))
    for b in (7, -7, 15, -15, 39, -39, 455, -455, 23, -23):
        B, m = gen_from_beta(rng, b)
        if B is not None:
            out.append((B, m, 'min', 'small b=%d' % b))
    for b in (7, -15, 39, -455, 31, -47):
        B, m = gen_theta_one(rng, b)
        if B is not None:
            out.append((B, m, 'min', 'small th=1 b=%d' % b))
    return out[:30]
