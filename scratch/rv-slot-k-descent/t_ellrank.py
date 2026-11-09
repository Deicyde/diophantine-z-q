"""Small realizations of the slot construction (data (beta, theta) with (theta1)-(theta4), not from an
admissible B; slots = smallest primes meeting the conditions of slot-k 2.4).  For each, certify both
curves with sel2.py and run PARI ellrank; for every point found, test whether its abscissa class is
beta times a torsion first coordinate (1, -1, d, -d)."""
import random

import cypari2
import gmpy2

from sel2 import selmer, first_coord_contains

pari = cypari2.Pari()
pari.allocatemem(10 ** 9)


def leg(a, p):
    return 0 if gmpy2.legendre(a % p, p) == 1 else 1


def primes_from(start):
    p = start
    while True:
        p = int(gmpy2.next_prime(p))
        yield p


def smallest(c8, conds, used, start=10):
    for r in primes_from(start):
        if r % 8 == c8 and r not in used and all(leg(r, y) == b for y, b in conds):
            return r


def sqf(n):
    s = -1 if n < 0 else 1
    f = pari.factor(abs(n))
    for p, e in zip(f[0], f[1]):
        if int(e) % 2:
            s *= int(p)
    return s


def instance(beta, theta):
    P = [int(p) for p in pari.factor(abs(beta))[0]]
    T = [int(p) for p in pari.factor(theta)[0]] if theta > 1 else []
    lam = lambda p: p % 4 == 3
    s = int(beta < 0); x = 1 - s; p0 = P[0]
    used = set(P) | set(T)
    conds = [(p, (1 + lam(p) * x) % 2) for p in P[1:]]
    conds.append((p0, (x + sum(b for _, b in conds)) % 2))
    q0 = smallest(3, conds + [(l, 0) for l in T], used); used.add(q0)
    RP = []
    for p in P[1:]:
        c = [(p, 1), (p0, 1), (q0, 0)] + [(y, 0) for y in P if y not in (p, p0)] + [(l, 0) for l in T]
        c += [(r, 0) for r in RP]
        r = smallest(1, c, used); RP.append(r); used.add(r)
    RT = []
    for l in T:
        c = [(l, 1), (q0, 1)] + [(y, 0) for y in P] + [(y, 0) for y in T if y != l] + [(r, 0) for r in RP + RT]
        r = smallest(1, c, used); RT.append(r); used.add(r)
    pr = sorted(P + [q0] + RP + RT)
    d1 = 1
    for p in pr:
        d1 *= p
    return pr, d1, sorted(pr + T), d1 * theta


def ok_pair(beta, theta):
    if theta % 8 != 1 or gmpy2.gcd(theta, 2730) != 1 or gmpy2.gcd(beta, theta) != 1:
        return False
    P = [int(p) for p in pari.factor(abs(beta))[0]]
    T = [int(p) for p in pari.factor(theta)[0]] if theta > 1 else []
    return all(leg(beta, l) == 0 for l in T) and all(leg(theta, p) == 0 for p in P)


def main():
    rng = random.Random(7)
    cands = []
    smallp = [p for p in range(11, 200) if gmpy2.is_prime(p)]
    while len(cands) < 5:
        b = rng.choice(smallp) * (rng.choice([1, 3, 5, 7, 13]) if rng.random() < 0.5 else 1)
        b = sqf(b) * rng.choice((1, -1))
        if abs(b) % 8 != 7:
            continue
        th = 1
        for _ in range(rng.randrange(1, 3)):
            th *= rng.choice(smallp)
        if sqf(th) == th and ok_pair(b, th):
            cands.append((b, th))
    for beta, theta in cands:
        pr1, d1, pr2, d2 = instance(beta, theta)
        for d, pr in ((d1, pr1), (d2, pr2)):
            gens, ker = selmer(d, pr, seed=d % 1000)
            E = pari.ellinit([0, 0, 0, -d * d, 0])
            r = pari.ellrank(E, 3)
            pts = [p for p in r[3]]
            cls = []
            for P in pts:
                xx = pari.numerator(P[0]) * pari.denominator(P[0])
                cls.append(any(sqf(int(xx) * t) == beta for t in (1, -1, d, -d)))
            print("beta=%d theta=%d d=%d primes=%s dimSel2=%d beta_in_pi1=%s ellrank[r1,r2,s]=%s points=%d "
                  "abscissa class beta*torsion: %s" % (beta, theta, d, pr, len(ker),
                  first_coord_contains(gens, ker, beta), [int(t) for t in r[:3]], len(pts), cls), flush=True)


if __name__ == "__main__":
    main()
