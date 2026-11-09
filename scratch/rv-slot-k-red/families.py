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
