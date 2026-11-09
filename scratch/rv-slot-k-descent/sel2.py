"""Independent exact 2-Selmer group of C_d : y^2 = x^3 - d^2 x, d > 0 odd squarefree.

Method (no use of Proposition 0):
- Kummer map P -> (x, x - d) into Q(S,2)^2, S = {-1, 2, primes of d}.
- For each place v in {oo, 2, p | d} the local image I_v is computed from genuine local points:
  rationals x with x(x-d)(x+d) a nonzero square in Q_v.  Sampling stops once the span reaches the
  known size dim I_v = 1 (oo), 3 (2), 2 (odd p); a larger span would be an error.
- Places p not dividing 2d impose nothing on classes supported on S (good reduction, unramified).
- Sel_2 = {sigma in Q(S,2)^2 : loc_v(sigma) in I_v for all v}, by F_2 linear algebra.
Local coordinates: oo -> sign bit; 2 -> (v, eps, omega) of w = 2^v u, eps = (u-1)/2, omega = (u^2-1)/8;
odd p -> (v mod 2, [u/p]).
"""
import random
from fractions import Fraction as Fr

import gmpy2


def vp(n, p):
    n = abs(n); k = 0
    while n % p == 0:
        n //= p; k += 1
    return k, n


def loc_odd(w, p):
    """w nonzero Fraction -> (v mod 2, symbol bit of unit part) in Q_p*/Q_p*^2."""
    s = -1 if w < 0 else 1
    vn, un = vp(w.numerator, p); vd, ud = vp(w.denominator, p)
    u = s * un * ud  # same square class as s*un/ud
    return ((vn - vd) & 1, 0 if gmpy2.legendre(u % p, p) == 1 else 1)


def loc_two(w):
    s = -1 if w < 0 else 1
    vn, un = vp(w.numerator, 2); vd, ud = vp(w.denominator, 2)
    u = (s * un * ud) % 8
    return ((vn - vd) & 1, ((u - 1) // 2) & 1, ((u * u - 1) // 8) & 1)


def loc_real(w):
    return (1 if w < 0 else 0,)


def is_local_square(w, place):
    if w == 0:
        return False
    if place == 'oo':
        return w > 0
    if place == 2:
        vn, un = vp(w.numerator, 2); vd, ud = vp(w.denominator, 2)
        return (vn - vd) % 2 == 0 and ((-1 if w < 0 else 1) * un * ud) % 8 == 1
    v, sym = loc_odd(w, place)
    return v == 0 and sym == 0


def loc(w, place):
    if place == 'oo':
        return loc_real(w)
    if place == 2:
        return loc_two(w)
    return loc_odd(w, place)


def bits(t):
    out = 0
    for i, b in enumerate(t):
        out |= b << i
    return out


class Span:
    """F_2 span of int bitvectors, reduced echelon by leading bit."""
    def __init__(self):
        self.rows = {}

    def reduce(self, x):
        while x:
            h = x.bit_length() - 1
            if h in self.rows:
                x ^= self.rows[h]
            else:
                return x
        return 0

    def add(self, x):
        x = self.reduce(x)
        if x:
            self.rows[x.bit_length() - 1] = x
            return True
        return False

    def dim(self):
        return len(self.rows)


LOCDIM = {'oo': 1, 2: 3}


def local_image(d, place, rng, budget=20000):
    """Span (in bits of loc(x) | loc(x-d)) of the local image, from genuine local points."""
    want = LOCDIM.get(place, 2)
    nb = 1 if place == 'oo' else (3 if place == 2 else 2)
    sp = Span()
    p = place
    for it in range(budget):
        k = rng.randrange(6)
        a = rng.randrange(1, 10 ** 6) * rng.choice((1, -1))
        if p == 'oo':
            x = Fr(rng.randrange(-4 * d, 4 * d + 1), rng.randrange(1, 7))
        else:
            q = 2 if p == 2 else p
            e = rng.randrange(-3, 4)
            base = [0, d, -d][rng.randrange(3)]
            x = base + Fr(a) * Fr(q) ** e if rng.random() < 0.8 else Fr(a, rng.randrange(1, 10 ** 6))
        if x in (0, d, -d):
            continue
        f = x * (x - d) * (x + d)
        if not is_local_square(f, p):
            continue
        cls = bits(loc(x, p) + loc(x - d, p))
        sp.add(cls)
        if sp.dim() > want:
            raise RuntimeError("local image too large at %s" % (p,))
        if sp.dim() == want and it > 50:
            return sp, nb
    raise RuntimeError("local image incomplete at %s (dim %d)" % (p, sp.dim()))


def annihilator(sp, nb):
    """Rows h in F_2^{2nb} with h.x = 0 for x in sp (brute force; 2nb <= 6)."""
    n = 2 * nb
    hs = Span()
    basis = list(sp.rows.values())
    for h in range(1, 1 << n):
        if all(bin(h & x).count('1') % 2 == 0 for x in basis):
            hs.add(h)
    assert hs.dim() == n - sp.dim()
    return list(hs.rows.values())


def selmer(d, primes, seed=0):
    """Return (basis gens list, list of kernel vectors) for Sel_2(C_d).
    Vector layout: bits 0..g-1 = exponents of a on gens, bits g..2g-1 = exponents of b."""
    assert d > 0 and d % 2 == 1
    rng = random.Random(seed)
    gens = [-1, 2] + list(primes)
    g = len(gens)
    places = ['oo', 2] + list(primes)
    conds = []  # each condition: int over 2g bits
    for pl in places:
        sp, nb = local_image(d, pl, rng)
        H = annihilator(sp, nb)
        locg = [bits(loc(Fr(x), pl)) for x in gens]
        for h in H:
            ha, hb = h & ((1 << nb) - 1), h >> nb
            row = 0
            for i in range(g):
                if bin(ha & locg[i]).count('1') & 1:
                    row |= 1 << i
                if bin(hb & locg[i]).count('1') & 1:
                    row |= 1 << (g + i)
            conds.append(row)
    return gens, kernel(conds, 2 * g)


def kernel(rows, n):
    """Basis of {x in F_2^n : r.x = 0 for all rows}."""
    piv = {}  # pivot col -> row (reduced)
    for r in rows:
        for c, pr in piv.items():
            if r >> c & 1:
                r ^= pr
        if r:
            c = (r & -r).bit_length() - 1
            for c2 in list(piv):
                if piv[c2] >> c & 1:
                    piv[c2] ^= r
            piv[c] = r
    free = [c for c in range(n) if c not in piv]
    basis = []
    for f in free:
        x = 1 << f
        for c, pr in piv.items():
            if pr >> f & 1:
                x |= 1 << c
        basis.append(x)
    return basis


def vec_a(a, gens):
    """Exponent bitvector of a squarefree integer a on gens (-1, 2, primes)."""
    x = 0
    if a < 0:
        x |= 1
        a = -a
    for i, q in enumerate(gens[1:], start=1):
        if a % q == 0:
            x |= 1 << i
            a //= q
    assert a == 1, "a not supported on gens"
    return x


def first_coord_contains(gens, ker, a):
    """Is a (squarefree, supported on gens) the first coordinate of some Selmer class?"""
    g = len(gens)
    target = vec_a(a, gens)
    mask = (1 << g) - 1
    sp = Span()
    for k in ker:
        sp.add(k & mask)
    return sp.reduce(target) == 0
