"""The Selmer system Sigma(C) of slot-k section 2.1 (descent-alt Proposition 0), implemented from
the text, for an abstract configuration: classes c[x] in {1,3,5,7}, symbols L[x][y] = [y/x].
Unknowns ordered: a0, a1, b0, b1, u_x (x in S), v_x (x in S)."""
from sel2 import span, leg


def lam(c): return 1 if c % 4 == 3 else 0
def mu(c): return 1 if c % 8 in (3, 5) else 0


def solve_system(S, c, L):
    """S: list of labels; c: dict label->class mod 8; L: dict (x,y)->[y/x] for x != y.
    returns (dim, kernel basis as ints).  bit layout: 0 a0, 1 a1, 2 b0, 3 b1, 4.. u, 4+k.. v."""
    k = len(S)
    idx = {x: i for i, x in enumerate(S)}
    U = lambda x: 1 << (4 + idx[x])
    V = lambda x: 1 << (4 + k + idx[x])
    A0, A1, B0, B1 = 1, 2, 4, 8
    rows = []
    ct = 1
    for x in S:
        ct = ct * c[x] % 8
    for x in S:
        lx, mx = lam(c[x]), mu(c[x])
        r1 = 0
        r2 = 0
        for y in S:
            if y == x:
                continue
            if L[(x, y)]:
                r1 ^= U(y) ^ U(x)
                r2 ^= V(y) ^ V(x)
        if lx:
            r1 ^= V(x) ^ A0
            r2 ^= V(x) ^ B0
        if mx:
            r1 ^= A1
            r2 ^= U(x) ^ B1
        rows += [r1, r2]
    rows.append(A0 ^ B0)
    lu = mu_u = lv = 0
    for x in S:
        if lam(c[x]):
            lu ^= U(x); lv ^= V(x)
        if mu(c[x]):
            mu_u ^= U(x)
    if ct == 1:
        rows += [A1, mu_u, lv ^ lu]
    elif ct == 3:
        rows += [A1, B0 ^ lv, B1 ^ mu_u]
    elif ct == 5:
        rows += [A1, B1 ^ mu_u, lv ^ lu]
    else:
        rows += [A1, mu_u, B0 ^ lv]
    n = 4 + 2 * k
    R = span(rows)
    free = [j for j in range(n) if j not in R]
    ker = []
    for f in free:
        v = 1 << f
        for piv, r in R.items():
            if r >> f & 1:
                v |= 1 << piv
        ker.append(v)
    return len(ker), ker


def config_of(ps):
    """configuration of the odd positive squarefree number with prime list ps."""
    c = {p: p % 8 for p in ps}
    L = {(x, y): leg(y, x) for x in ps for y in ps if x != y}
    return ps, c, L


def a_vector(a0, a1, uset, S):
    """the 'first coordinate' part of the bit layout: bits a0,a1 and u."""
    v = a0 | (a1 << 1)
    for i, x in enumerate(S):
        if x in uset:
            v |= 1 << (4 + i)
    return v


def first_coord_mask(k):
    m = 3
    for i in range(k):
        m |= 1 << (4 + i)
    return m


def contains_first(ker, target, k):
    from sel2 import reduce
    mask = first_coord_mask(k)
    return reduce(target, span([v & mask for v in ker])) == 0
