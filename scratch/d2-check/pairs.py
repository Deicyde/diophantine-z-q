"""Draw admissible pairs (B, m) with omega(beta) <= 3, |beta| = 7 (mod 8), beta odd, theta < 10^6.

Construction: beta (odd squarefree, omega <= 3, primes < 200, |beta| = 7 mod 8) and theta
(squarefree, = 1 mod 8, prime to 2730*beta, a square mod 3, 5, 7, 13 (needed for p not dividing D), log-uniform in [17, 10^6)) at random; a primitive
solution of D^2 - theta Y^2 = beta (2730^2 c')^2 (PARI qfsolve + qfparam, random parameter u/v near a real root of c(u, v));
m a random signed divisor of 2730 with sign(m) = sign(beta); B = m beta c^2 / D^2, c = 2730^2 c'.
Then sqf(mB) = beta and sqf(m(m - B)) = theta.  Admissibility and both square classes are
re-checked with descent_search.admissible / sqfQ.
Usage: python pairs.py COUNT SEED > pairs.json"""
import os, sys, json, random
from fractions import Fraction as Fr
from math import gcd
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "rv-route-k"))
import descent_search as ds  # admissible, sqfQ, factor, DIVS
pari = ds.pari

SMALLP = [int(p) for p in pari.primes(46)][1:]  # odd primes < 200


def sqfree(n):
    return all(e == 1 for e in ds.factor(n).values())


def rand_beta(rng):
    while True:
        k = rng.randint(1, 3)
        ps = rng.sample(SMALLP, k)
        b = 1
        for p in ps:
            b *= p
        b *= rng.choice((1, -1))
        if abs(b) % 8 == 7:
            return b


def rand_theta(rng, beta):
    while True:
        t = int(10 ** rng.uniform(1.23, 6))
        if (t % 8 == 1 and gcd(t, 2730 * beta) == 1 and sqfree(t)
                and all(pow(t % p, (p - 1) // 2, p) == 1 for p in (3, 5, 7, 13))):
            return t


def draw(rng):
    K = 2730 ** 2
    while True:
        beta = rand_beta(rng)
        theta = rand_theta(rng, beta)
        G = pari.matdiagonal([1, -theta, -beta * K * K])
        s = pari.qfsolve(G)
        if str(pari.type(s)) != 't_COL':
            continue
        Q = pari.qfparam(G, s)  # 3x3: rows = coefficients of (u^2, uv, v^2)
        a2, a1, a0 = int(Q[2, 0]), int(Q[2, 1]), int(Q[2, 2])
        disc = a1 * a1 - 4 * a2 * a0
        if disc < 0 or a2 == 0:
            continue
        # u/v near a real root of c(u, v) = 0, so that beta c^2 is small against D^2 (B < 1/2)
        roots = [(-a1 + sg * disc ** 0.5) / (2 * a2) for sg in (1, -1)]
        for _ in range(400):
            v = rng.randrange(1, 10 ** 4)
            u = round(rng.choice(roots) * v) + rng.randrange(-3, 4)
            x = [int(Q[i, 0]) * u * u + int(Q[i, 1]) * u * v + int(Q[i, 2]) * v * v for i in range(3)]
            g = gcd(gcd(x[0], x[1]), x[2])
            if g == 0:
                continue
            D, Y, cp = (abs(t // g) for t in x)
            if cp == 0 or D == 0:
                continue
            c = K * cp
            assert D * D - theta * Y * Y == beta * c * c
            ms = [m for m in ds.DIVS if (m > 0) == (beta > 0)]
            rng.shuffle(ms)
            for m in ms:
                B = Fr(m * beta * c * c, D * D)
                if B.denominator != D * D or not ds.admissible(B):
                    continue
                if ds.sqfQ(m * B) == beta and ds.sqfQ(m * (m - B)) == theta:
                    return dict(B=str(B), m=m, beta=beta, theta=theta)


if __name__ == "__main__":
    count, seed = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(seed)
    out = []
    for i in range(count):
        r = draw(rng)
        out.append(r)
        print(i, r["m"], r["beta"], r["theta"], len(r["B"]), file=sys.stderr, flush=True)
    json.dump(out, sys.stdout, indent=0)
