"""Complete 2-descent for E_N^{a,b}: y^2 = x(x - aN)(x - bN) and the simultaneous
descent of Section 5.1, for the pi/3 family (a,b) = (1,-3) (the manuscript's E_N) and
the congruent-number family (a,b) = (1,-1).

Kummer map: P -> (x, x - aN) in (Q*/Q*^2)^2.  The 2-Selmer group is computed exactly:
candidates are supported on S = {-1} u {primes of 2*(a-b)*N}; local images are the span
of the 2-torsion at odd primes p | N (p not dividing 2(a-b)), the unramified classes at
good odd primes (automatic for candidates supported on S), and are found by p-adic
sampling at p | 2(a-b) and at infinity (sign conditions).

For a pole input B we take m > 0 dividing 2730, beta = sqf(mB), theta = sqf(m(m - B)),
and search n = beta * n' (n' a product of small auxiliary primes) such that both
E_n and E_{n theta} have dim Sel_2 = 3 and contain a class with first coordinate beta.

Usage: python selmer_descent.py FAMILY NUM_SAMPLES SEED    (FAMILY in {pi3, cong})
"""
import sys
import random
import itertools
from fractions import Fraction as F
from math import isqrt, gcd
import cypari2

pari = cypari2.Pari()
pari.allocatemem(2 * 10**9)

FAMILIES = {"pi3": (1, -3), "cong": (1, -1)}


def factor_primes(n):
    n = abs(int(n))
    if n <= 1:
        return []
    return [int(p) for p in pari.factor(n)[0]]


def core(n):
    n = F(n)
    return int(pari.core(int(n.numerator) * int(n.denominator)))


def vp(n, p):
    n = abs(int(n))
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k


def vq(q, p):
    q = F(q)
    return vp(q.numerator, p) - vp(q.denominator, p)


def sqclass(q, p):
    """Squareclass of nonzero rational q in Q_p^*/Q_p^*2 as a hashable tuple; p=0 is R."""
    q = F(q)
    if p == 0:
        return (q > 0,)
    k = vq(q, p)
    u = q / F(p) ** k
    num, den = u.numerator, u.denominator
    if p == 2:
        return (k % 2, (num * den) % 8)
    leg = pow(num * den % p, (p - 1) // 2, p)
    return (k % 2, leg == 1)


def is_local_square(q, p):
    c = sqclass(q, p)
    if p == 0:
        return c == (True,)
    if p == 2:
        return c == (0, 1)
    return c == (0, True)


def local_image(N, a, b, p, rng, want):
    """Image of E(Q_p) in (Q_p*/Q_p*2)^2 under P -> (x, x - aN), by sampling.
    `want` is the expected size (|E(Q_p)[2]| * |2|_p^{-1}, i.e. 8 at p = 2, 4 at odd p,
    2 at the real place for three real roots)."""
    img = set()
    roots = [0, a * N, b * N]
    # images of the 2-torsion
    for i, e in enumerate(roots):
        others = [r for r in roots if r != e]
        first = (e - roots[1]) * (e - roots[2]) if i == 0 else e
        second = (e - roots[0]) * (e - roots[2]) if i == 1 else e - roots[1]
        img.add((sqclass(first, p), sqclass(second, p)))
    img.add((sqclass(1, p), sqclass(1, p)))
    tries = 0
    pp = p if p else 7
    while len(img) < want and tries < 200000:
        tries += 1
        k = rng.randrange(-6, 7)
        x = F(rng.randrange(-pp**4, pp**4 + 1), rng.randrange(1, pp**3)) * F(pp) ** k if p else F(rng.randrange(-10**6, 10**6), rng.randrange(1, 10**3)) * N
        if x == 0 or x == a * N or x == b * N:
            continue
        fx = x * (x - a * N) * (x - b * N)
        if is_local_square(fx, p):
            img.add((sqclass(x, p), sqclass(x - a * N, p)))
    # close under multiplication (the image is a group)
    changed = True
    while changed:
        changed = False
        for u in list(img):
            for v in list(img):
                w = mult(u, v, p)
                if w not in img:
                    img.add(w)
                    changed = True
    return img


def mult(u, v, p):
    return tuple(mult1(u[i], v[i], p) for i in range(2))


def mult1(c, d, p):
    if p == 0:
        return (c[0] == d[0],)
    if p == 2:
        return ((c[0] + d[0]) % 2, (c[1] * d[1]) % 8)
    return ((c[0] + d[0]) % 2, c[1] == d[1])


def vec_local(q, p):
    """F_2 coordinates of the squareclass of q at p (list of bits)."""
    c = sqclass(q, p)
    if p == 0:
        return [0 if c[0] else 1]
    if p == 2:
        k, u = c
        return [k, 1 if u in (3, 7) else 0, 1 if u in (3, 5) else 0]
    return [c[0], 0 if c[1] else 1]


def vec_pair(u, p):
    """Bits of a pair of local squareclasses given as sqclass tuples."""
    out = []
    for c in u:
        if p == 0:
            out += [0 if c[0] else 1]
        elif p == 2:
            k, w = c
            out += [k, 1 if w in (3, 7) else 0, 1 if w in (3, 5) else 0]
        else:
            out += [c[0], 0 if c[1] else 1]
    return out


def tobits(v):
    x = 0
    for i, e in enumerate(v):
        if e:
            x |= 1 << i
    return x


def rref_basis(vecs):
    """Row-reduced basis (dict pivot->vector) of the span of integer bitvectors."""
    basis = {}
    for v in vecs:
        for piv in sorted(basis, reverse=True):
            if v >> piv & 1:
                v ^= basis[piv]
        if v:
            piv = v.bit_length() - 1
            for q in list(basis):
                if basis[q] >> piv & 1:
                    basis[q] ^= v
            basis[piv] = v
    return basis


def reduce(v, basis):
    for piv in sorted(basis, reverse=True):
        if v >> piv & 1:
            v ^= basis[piv]
    return v


def selmer_space(N, a, b, rng):
    """Return (gens, kernel basis as bitvectors over 2*len(gens) coordinates)."""
    S = sorted(set(factor_primes(2 * a * b * (a - b) * N)) | {2})
    gens = [-1] + S
    g = len(gens)
    places = S + [0]
    cond_rows = []          # each row: bitvector over 2g coordinates; Selmer = common kernel
    for p in places:
        want = 2 if p == 0 else (8 if p == 2 else 4)
        img = local_image(N, a, b, p, rng, want)
        if len(img) != want:
            raise RuntimeError(f"local image at {p}: {len(img)} != {want}")
        imgb = rref_basis([tobits(vec_pair(u, p)) for u in img])
        loc_dim = len(vec_pair(next(iter(img)), p))
        # images of the generators in each coordinate
        gv = [tobits(vec_local(x, p)) for x in gens]
        half = loc_dim // 2
        # local map L: F_2^{2g} -> F_2^{loc_dim}; column j<g -> gv[j], column g+j -> gv[j] << half
        cols = [gv[j] for j in range(g)] + [gv[j] << half for j in range(g)]
        # complement coordinates: functionals vanishing on the image.  Compute by
        # reducing each column modulo the image and collecting the residues.
        res = [reduce(c, imgb) for c in cols]
        # residues live in a complement; rows = coordinates of residues
        for bit in range(loc_dim):
            row = 0
            for j, r in enumerate(res):
                if r >> bit & 1:
                    row |= 1 << j
            if row:
                cond_rows.append(row)
    # kernel of the condition rows over F_2^{2g}
    piv = rref_basis(cond_rows)
    pivcols = set(piv)
    # rref_basis pivots on highest bit; build kernel basis by free variables
    free = [j for j in range(2 * g) if j not in pivcols]
    kernel = []
    for f in free:
        v = 1 << f
        for pc, row in piv.items():
            if row >> f & 1:
                v |= 1 << pc
        kernel.append(v)
    return gens, kernel


def selmer_dim(N, a, b, rng):
    gens, ker = selmer_space(N, a, b, rng)
    return len(ker), gens, ker


def class_with_first(gens, ker, beta):
    """Is there a Selmer element whose first coordinate is the class of beta?"""
    g = len(gens)
    # vector of beta over gens (beta must be supported on gens)
    t = 0
    rest = beta
    if rest < 0:
        t |= 1
        rest = -rest
    for j, p in enumerate(gens[1:], start=1):
        if rest % p == 0:
            rest //= p
            t |= 1 << j
    if core(rest) != 1:
        return False
    mask = (1 << g) - 1
    firsts = rref_basis([v & mask for v in ker])
    return reduce(t, firsts) == 0


def random_admissible_B(rng):
    K = 2**4 * 3**6 * 5**6 * 7**6 * 13**6
    u = rng.randrange(1, 10**3)
    lo = isqrt(2 * K * u) + 1
    v = rng.randrange(lo, 4 * lo)
    return F(K * u, v * v)


def search_n(B, a, b, rng, primes, max_aux=3, max_m=None):
    divs = [d for d in range(1, 2731) if 2730 % d == 0]
    for m in divs:
        beta = core(m * B)
        theta = core(m * (m - B))
        if beta <= 1 or len(factor_primes(beta)) > 4 or len(factor_primes(theta)) > 5:
            continue
        pool = [q for q in primes if beta % q and theta % q and q > 3]
        for k in range(0, max_aux + 1):
            for combo in itertools.combinations(pool[:14], k):
                nprime = 1
                for q in combo:
                    nprime *= q
                n = beta * nprime
                try:
                    d1, g1, k1 = selmer_dim(n, a, b, rng)
                    if d1 != 3 or not class_with_first(g1, k1, beta):
                        continue
                    d2, g2, k2 = selmer_dim(n * theta, a, b, rng)
                    if d2 != 3 or not class_with_first(g2, k2, beta):
                        continue
                except RuntimeError as e:
                    print('  local image failure:', e, flush=True)
                    continue
                return m, beta, theta, combo
    return None


if __name__ == "__main__":
    fam = sys.argv[1]
    a, b = FAMILIES[fam]
    N = int(sys.argv[2])
    seed = int(sys.argv[3])
    rng = random.Random(seed)
    primes = [int(p) for p in pari.primes(60)][2:]
    ok = 0
    for i in range(N):
        B = random_admissible_B(rng)
        res = search_n(B, a, b, rng, primes)
        print(i, fam, "B =", B, "->", res, flush=True)
        ok += res is not None
    print(f"{fam}: simultaneous Selmer-minimal n found for {ok}/{N} inputs")
