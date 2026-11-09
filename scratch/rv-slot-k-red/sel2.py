"""Independent exact 2-Selmer group of C_d : y^2 = x^3 - d^2 x, d > 0 odd squarefree.

Written from the definition, not from Proposition 0 and not from scratch/slot-k or descent-alt:
  Sel_2(C_d) = {(a, b) in <-1, 2, p | d>^2 : the local class of (a, b) lies in the local image at
               every place v in {oo, 2, p | d}}
(classes supported on -1, 2 and the primes of d are unramified outside 2d, where the condition is
automatic).  Kummer map P -> (x, x - d); torsion images (0,0)->(-1,-d), (d,0)->(d,2).
Local images:
  * odd p | d : span of the two torsion images (#E(Q_p)/2E(Q_p) = 4 and they are independent);
  * oo        : span of (-1,-d) = (sign -, sign -);
  * 2         : computed by searching 2-adic points (x rational, x(x-d)(x+d) a nonzero 2-adic
                square) together with torsion, until the span has dimension 3 = log2 #E(Q_2)/2E(Q_2).
Linear algebra over F_2 with python ints as bit vectors.
"""
from fractions import Fraction as Fr
import gmpy2


def leg(a, p):
    """[a/p] in F_2 for an odd prime p not dividing a."""
    j = gmpy2.jacobi(a % p, p)
    assert j != 0, (a, p)
    return 0 if j == 1 else 1


def v_p(n, p):
    n = abs(n); k = 0
    while n % p == 0:
        n //= p; k += 1
    return k


def cls_2(r):
    """class of a nonzero rational in Q_2*/Q_2*^2 as (v mod 2, eps, omega)."""
    r = Fr(r)
    num, den = r.numerator, r.denominator
    v = v_p(num, 2) - v_p(den, 2)
    u = (num >> v_p(num, 2)) * (den >> v_p(den, 2))  # odd, same class as unit part (den^2 trick not needed mod 8? use u*den^2)
    # unit part = num'/den' ; class of num'/den' = class of num'*den' since den'^2 is a square
    u %= 8
    return (v & 1, ((u - 1) // 2) & 1, ((u * u - 1) // 8) & 1)


def cls_p(r, p):
    r = Fr(r)
    num, den = r.numerator, r.denominator
    a, b = v_p(num, p), v_p(den, p)
    unit = (num // p**a) * (den // p**b)
    return ((a - b) & 1, leg(unit, p))


def is_sq_2(r):
    c = cls_2(r)
    return c == (0, 0, 0)


def span(vecs):
    """row-reduced basis (dict pivot->vec) of span of int bit vectors."""
    basis = {}
    for v in vecs:
        for piv in sorted(basis, reverse=True):
            if v >> piv & 1:
                v ^= basis[piv]
        if v:
            piv = v.bit_length() - 1
            for k in list(basis):
                if basis[k] >> piv & 1:
                    basis[k] ^= v
            basis[piv] = v
    return basis


def reduce(v, basis):
    for piv in sorted(basis, reverse=True):
        if v >> piv & 1:
            v ^= basis[piv]
    return v


def pack(bits):
    v = 0
    for i, b in enumerate(bits):
        v |= (b & 1) << i
    return v


_img2_cache = {}


def image_2(d):
    """basis of the image of C_d(Q_2)/2 in (Q_2*/Q_2*^2)^2, as 6-bit ints (a-bits 0..2, b-bits 3..5).
    Computed from points of C_d itself; cached by d mod 8 only after checking (the image depends
    only on the 2-adic class of d, which for odd d > 0 is d mod 8)."""
    def enc(a, b):
        return pack(cls_2(a) + cls_2(b))
    vecs = [enc(-1, -d), enc(d, 2)]
    found = []
    for j in range(-4, 5):
        for a in range(-200, 201):
            if a == 0:
                continue
            x = Fr(a) * Fr(4) ** j
            if x == d or x == -d:
                continue
            f = x * (x - d) * (x + d)
            if is_sq_2(f):
                vecs.append(enc(x, x - d))
                found.append(x)
        if len(span(vecs)) == 3:
            break
    B = span(vecs)
    assert len(B) == 3, (d, len(B))
    return B


def selmer(d):
    """returns (dim, basis list of (a_bits, b_bits) over generator list gens, gens).
    gens = [-1, 2, p1, ..., pk]; an element is an int with a-exponents in bits 0..n-1 and
    b-exponents in bits n..2n-1."""
    import sympy
    assert d > 0 and d % 2 == 1
    ps = sorted(sympy.factorint(d).keys()) if not isinstance(d, tuple) else None
    return selmer_primes(d, ps)


def selmer_primes(d, ps):
    gens = [-1, 2] + list(ps)
    n = len(gens)
    # each place: list of (local class vector per generator for a, and for b), image basis
    rows = []  # linear functionals on F_2^{2n}
    places = [('oo', None), ('2', None)] + [('p', p) for p in ps]
    for kind, p in places:
        if kind == 'oo':
            loc = lambda g: [1 if g < 0 else 0]
            img = span([pack([1, 1])])  # (-1,-d): signs (-,-); d>0
            dim = 1
        elif kind == '2':
            loc = lambda g: list(cls_2(g))
            img = image_2(d)
            dim = 3
        else:
            loc = (lambda p: (lambda g: list(cls_p(g, p))))(p)
            img = span([pack(list(cls_p(-1, p)) + list(cls_p(-d, p))),
                        pack(list(cls_p(d, p)) + list(cls_p(2, p)))])
            dim = 2
        # local map M: F_2^{2n} -> F_2^{2dim}: column for generator i (a-part) and n+i (b-part)
        cols = []
        for i, g in enumerate(gens):
            cols.append(pack(loc(g) + [0] * dim))
        for i, g in enumerate(gens):
            cols.append(pack([0] * dim + loc(g)))
        # functionals annihilating img: compute basis of img^perp in F_2^{2dim}
        perp = []
        for f in range(1, 1 << (2 * dim)):
            if all(bin(f & v).count('1') % 2 == 0 for v in img.values()):
                perp.append(f)
        perp_b = span(perp)
        assert len(perp_b) == 2 * dim - len(img)
        for f in perp_b.values():
            row = 0
            for j, c in enumerate(cols):
                if bin(f & c).count('1') % 2:
                    row |= 1 << j
            rows.append(row)
    # kernel of rows on F_2^{2n}
    R = span(rows)
    pivots = set(R)
    free = [j for j in range(2 * n) if j not in pivots]
    kernel = []
    for fcol in free:
        v = 1 << fcol
        for piv, r in R.items():
            # r has pivot piv (highest bit); fully reduced; solve x_piv = sum r_j x_j over free
            if r >> fcol & 1:
                v |= 1 << piv
        kernel.append(v)
    # sanity: every kernel vector satisfies all rows
    for v in kernel:
        for r in rows:
            assert bin(v & r).count('1') % 2 == 0
    return len(kernel), kernel, gens


def first_coords(kernel, gens):
    n = len(gens)
    mask = (1 << n) - 1
    return span([v & mask for v in kernel])


def vec_of(a, gens):
    """exponent vector of a squarefree integer a supported on gens."""
    v = 0
    if a < 0:
        v |= 1; a = -a
    for i, g in enumerate(gens[1:], start=1):
        if a % g == 0:
            v |= 1 << i; a //= g
    assert a == 1, a
    return v


def in_pi1(a, kernel, gens):
    return reduce(vec_of(a, gens), first_coords(kernel, gens)) == 0
