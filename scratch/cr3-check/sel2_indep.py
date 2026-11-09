"""Independent exact 2-Selmer group of C_d : y^2 = x^3 - d^2 x (d > 0 odd squarefree).

Written for the cr3-check task from the definition of Sel_2, without using the system of
Proposition 0, scratch/slot-k, scratch/descent-alt or scratch/rv-slot-k-proof.

Kummer map P -> (x, x - d) in (Q*/Q*^2)^2, with (0,0) -> (-1,-d), (d,0) -> (d,2), (-d,0) -> (-d,-2d).
Sel_2 = {(a, b) in Q(S,2)^2 : loc_v(a, b) in Im_v for v in {inf, 2, p | d}}, S = {2, p | d}
(at p outside 2d the image is the unramified classes, automatic for classes supported on S).

Every local image Im_v (v = inf, 2 and every odd p | d) is computed from genuine local points:
the three 2-torsion points and points x = t / p^(2j) (resp. x = d + t p^j, -d + t p^j, t p^j) found
by testing whether x(x-d)(x+d) is a square in Q_v. The span is accepted only when it reaches the
known dimension dim E(Q_v)/2E(Q_v) = dim E(Q_v)[2] + [v = 2] = 2 (odd p), 3 (v = 2), 1 (v = inf).
"""
from fractions import Fraction as Fr
import itertools


def vsplit(n, p):
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k, n


def leg(a, p):
    a %= p
    assert a
    return 0 if pow(a, (p - 1) // 2, p) == 1 else 1


def cls_p(r, p):
    """Class of nonzero rational r in Q_p*/Q_p*^2 as a 2-bit tuple (valuation, residue bit)."""
    r = Fr(r)
    va, ua = vsplit(r.numerator, p)
    vb, ub = vsplit(r.denominator, p)
    return ((va - vb) % 2, leg(ua * ub, p))


def cls_2(r):
    """Class in Q_2*/Q_2*^2: (valuation, unit mod 4 bit, unit mod 8 bit)."""
    r = Fr(r)
    va, ua = vsplit(r.numerator, 2)
    vb, ub = vsplit(r.denominator, 2)
    u = (ua * ub) % 8
    return ((va - vb) % 2, 1 if u % 4 == 3 else 0, 1 if u in (3, 5) else 0)


def cls_inf(r):
    return (1 if r < 0 else 0,)


def is_sq(r, v):
    if r == 0:
        return True
    c = cls_inf(r) if v == 'inf' else cls_2(r) if v == 2 else cls_p(r, v)
    return not any(c)


def cls(r, v):
    return cls_inf(r) if v == 'inf' else cls_2(r) if v == 2 else cls_p(r, v)


def tomask(bits):
    m = 0
    for i, b in enumerate(bits):
        m |= b << i
    return m


def reduce(basis, x):
    for piv, b in basis:
        if x >> piv & 1:
            x ^= b
    return x


def add(basis, x):
    x = reduce(basis, x)
    if x:
        piv = x.bit_length() - 1
        basis = [(q, b ^ x if b >> piv & 1 else b) for q, b in basis]
        basis.append((piv, x))
    return basis


def kummer(x, d):
    if x == 0:
        return (Fr(-1), Fr(-d))
    if x == d:
        return (Fr(d), Fr(2))
    if x == -d:
        return (Fr(-d), Fr(-2 * d))
    return (Fr(x), Fr(x - d))


def local_image(d, v):
    need = 1 if v == 'inf' else 3 if v == 2 else 2
    q = 2 if v == 'inf' else v
    basis = []
    def offer(x):
        nonlocal basis
        a, b = kummer(x, d)
        basis = add(basis, tomask(cls(a, v) + cls(b, v)))
    for x in (0, d, -d):
        offer(Fr(x))
    if len(basis) == need:
        return basis, need
    for j in range(-6, 7):
        for t in range(1, 400):
            for sgn in (1, -1):
                for c in (0, d, -d):
                    x = Fr(c) + sgn * Fr(t) * Fr(q) ** j
                    if x in (0, d, -d):
                        continue
                    f = x * (x - d) * (x + d)
                    if is_sq(f, v):
                        offer(x)
                        if len(basis) == need:
                            return basis, need
    raise RuntimeError("local image search failed: d=%d v=%s dim=%d" % (d, v, len(basis)))


def selmer(d, primes):
    """Return (gens, list of Selmer elements as pairs of exponent vectors over gens)."""
    assert d > 0 and d % 2 == 1
    gens = [-1, 2] + sorted(primes)
    g = len(gens)
    places = ['inf', 2] + sorted(primes)
    # candidate basis: e_i in first coordinate or in second coordinate (2g vectors)
    images = {}
    for v in places:
        W, need = local_image(d, v)
        assert len(W) == need
        images[v] = W
    # condition: for each v, class of (a, b) at v reduced mod W_v must be 0 (linear in (a,b))
    def cond(vec):
        out = []
        for v in places:
            a = Fr(1); b = Fr(1)
            for i in range(g):
                if vec[i]:
                    a *= gens[i]
                if vec[g + i]:
                    b *= gens[i]
            out.append(reduce(images[v], tomask(cls(a, v) + cls(b, v))))
        return tuple(out)
    # the condition map is linear (class is a homomorphism, reduction is linear): kernel by
    # Gaussian elimination on concatenated masks
    width = {v: (1 if v == 'inf' else 3 if v == 2 else 2) * 2 for v in places}
    def flat(vec):
        c = cond(vec)
        m, sh = 0, 0
        for v, x in zip(places, c):
            m |= x << sh
            sh += width[v]
        return m
    cols = []
    for j in range(2 * g):
        e = [0] * (2 * g)
        e[j] = 1
        cols.append((flat(e), 1 << j))
    piv = []
    ker = []
    for img, comb in cols:
        for pimg, pcomb, pb in piv:
            if img >> pb & 1:
                img ^= pimg
                comb ^= pcomb
        if img:
            piv.append((img, comb, img.bit_length() - 1))
        else:
            ker.append(comb)
    elems = []
    for coeffs in itertools.product((0, 1), repeat=len(ker)):
        m = 0
        for c, k in zip(coeffs, ker):
            if c:
                m ^= k
        vec = [(m >> j) & 1 for j in range(2 * g)]
        assert flat(vec) == 0
        elems.append(vec)
    return gens, elems, len(ker)


def first_coords(d, primes):
    """dim and the set of first coordinates (signed squarefree integers) of Sel_2(C_d)."""
    gens, elems, dim = selmer(d, primes)
    g = len(gens)
    firsts = set()
    for vec in elems:
        a = 1
        for i in range(g):
            if vec[i]:
                a *= gens[i]
        firsts.add(a)
    return dim, firsts


if __name__ == "__main__":
    for d in [5, 6 * 0 + 13, 21, 29, 37, 53, 157]:
        from sympy import primefactors
        print(d, first_coords(d, primefactors(d)))
