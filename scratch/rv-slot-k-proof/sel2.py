"""Exact 2-Selmer group of C_d : y^2 = x^3 - d^2 x, d > 0 odd squarefree with known primes.

Written independently of scratch/slot-k and scratch/descent-alt; it does not use the system of
Proposition 0. Kummer map P -> (x, x - d) in (Q*/Q*^2)^2. Candidate classes are vectors over the
basis -1, 2, p_1..p_k in each coordinate. The Selmer group is the set of candidates whose
restriction to every place in {inf, 2, p | d} lies in the local image. Local images:
- p | d odd: span of the torsion images (exact: dim E(Q_p)/2 = 2 and the images are independent);
  this is checked at run time;
- 2: span of images of 2-adic points found by search, until dimension 3 (= dim E(Q_2)/2);
- inf: span of torsion images (dimension 1 = dim E(R)/2 for d > 0).
Primes not dividing 2d impose only unramifiedness, automatic for the candidates.
"""
from fractions import Fraction


def legendre_bit(a, p):
    a %= p
    assert a != 0
    t = pow(a, (p - 1) // 2, p)
    return 0 if t == 1 else 1


def vval(n, p):
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k, n


# ---------- local classes of rationals ----------
def cls_odd(r, p):
    """(valuation mod 2, residue bit of unit part) of nonzero rational r at odd prime p."""
    r = Fraction(r)
    a, b = r.numerator, r.denominator
    va, ua = vval(a, p)
    vb, ub = vval(b, p)
    return ((va - vb) % 2, legendre_bit(ua * ub, p))


def cls_2(r):
    """(valuation mod 2, eps, omega) of nonzero rational r in Q_2*/Q_2*^2."""
    r = Fraction(r)
    a, b = r.numerator, r.denominator
    va, ua = vval(a, 2)
    vb, ub = vval(b, 2)
    u = (ua * ub) % 8  # ub^2 == 1 mod 8 so ua*ub has the class of ua/ub
    return ((va - vb) % 2, ((u - 1) // 2) % 2, ((u * u - 1) // 8) % 2)


def cls_inf(r):
    return (1 if r < 0 else 0,)


def is_2adic_square(r):
    r = Fraction(r)
    if r == 0:
        return True
    v, e, w = cls_2(r)
    return v == 0 and e == 0 and w == 0


# ---------- F2 linear algebra on int bitmasks ----------
def rref(rows):
    basis = []  # list of (pivotbit, row)
    for r in rows:
        for pb, b in basis:
            if r >> pb & 1:
                r ^= b
        if r:
            pb = r.bit_length() - 1
            basis = [(q, (b ^ r) if (b >> pb & 1) else b) for q, b in basis]
            basis.append((pb, r))
    return basis


def in_span(basis, r):
    for pb, b in basis:
        if r >> pb & 1:
            r ^= b
    return r == 0


def bits_to_int(bits):
    x = 0
    for i, t in enumerate(bits):
        x |= (t & 1) << i
    return x


def kernel(mat_cols, nvars):
    """mat_cols[j] = int bitmask image of basis vector j. Return basis of kernel (int masks)."""
    # Gaussian elimination tracking combinations.
    rows = [(mat_cols[j], 1 << j) for j in range(nvars)]
    piv = []
    ker = []
    for img, comb in rows:
        for pimg, pcomb, pb in piv:
            if img >> pb & 1:
                img ^= pimg
                comb ^= pcomb
        if img:
            piv.append((img, comb, img.bit_length() - 1))
        else:
            ker.append(comb)
    return ker


# ---------- the descent ----------
def local_image_2(d, need=3, maxk=8, maxu=4000):
    imgs = []
    pts = 0
    for k in range(0, maxk):
        den = 4 ** k
        for u in range(-maxu, maxu + 1):
            x = Fraction(u, den)
            if x == 0 or x == d or x == -d:
                continue
            f = x * (x - d) * (x + d)
            if is_2adic_square(f):
                v = cls_2(x) + cls_2(x - d)
                imgs.append(bits_to_int(v))
                pts += 1
                if len(rref(imgs)) == need:
                    return rref(imgs)
    raise RuntimeError("2-adic image search failed for d=%d" % d)


def torsion_images(d):
    return [(-1, -d), (d, 2), (-d, -2 * d)]


def selmer(d, primes):
    """Return (dim, basis) of Sel_2(C_d) as list of (a, b) rationals; primes = primes of d."""
    assert d > 0 and d % 2 == 1
    gens = [-1, 2] + list(primes)
    g = len(gens)
    nv = 2 * g
    places = ['inf', 2] + list(primes)
    # local images and quotient maps
    cols = [0] * nv
    shift = 0
    for v in places:
        if v == 'inf':
            cl = cls_inf
            W = rref([bits_to_int(cl(a) + cl(b)) for a, b in torsion_images(d)])
            assert len(W) == 1
            w = 1
        elif v == 2:
            cl = cls_2
            W = local_image_2(d)
            w = 3
        else:
            p = v
            cl = lambda r, p=p: cls_odd(r, p)
            W = rref([bits_to_int(cl(a) + cl(b)) for a, b in torsion_images(d)])
            assert len(W) == 2
            w = 2
        # quotient by W: reduce images against W, then express in complement coordinates
        Wpiv = {pb for pb, _ in W}
        free = [i for i in range(2 * w) if i not in Wpiv]
        for j in range(nv):
            coord, gi = divmod(j, g)
            z = cl(gens[gi])
            vec = bits_to_int(z + (0,) * w) if coord == 0 else bits_to_int((0,) * w + z)
            for pb, b in W:
                if vec >> pb & 1:
                    vec ^= b
            red = 0
            for t, i in enumerate(free):
                red |= (vec >> i & 1) << t
            cols[j] |= red << shift
        shift += len(free)
    ker = kernel(cols, nv)
    return len(ker), ker, gens


def vec_to_pair(vec, gens):
    g = len(gens)
    a = 1
    b = 1
    for j in range(2 * g):
        if vec >> j & 1:
            if j < g:
                a *= gens[j]
            else:
                b *= gens[j - g]
    return a, b


def first_coord_vec(a, gens):
    """Bit vector (first coordinate block) of squarefree integer a over gens."""
    bits = [0] * len(gens)
    if a < 0:
        bits[0] = 1
        a = -a
    if a % 2 == 0:
        bits[1] = 1
        a //= 2
    for i, p in enumerate(gens[2:]):
        if a % p == 0:
            bits[i + 2] = 1
            a //= p
    assert a == 1, "a not supported on gens"
    return bits_to_int(bits)


def has_first_coord(ker, gens, a):
    g = len(gens)
    mask = (1 << g) - 1
    target = first_coord_vec(a, gens)
    proj = rref([k & mask for k in ker])
    return in_span(proj, target)


if __name__ == "__main__":
    for d, ps in [(1, []), (5, [5]), (21, [3, 7]), (7, [7]), (3, [3]), (35, [5, 7]), (15, [3, 5])]:
        dim, ker, gens = selmer(d, ps)
        print(d, dim, [vec_to_pair(k, gens) for k in ker])
