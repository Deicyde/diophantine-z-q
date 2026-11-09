"""Own implementation of the Selmer system Sigma(C) of slot-k §2.1 for an abstract configuration.

A configuration: list of classes c[i] in {1,3,5,7} and a symbol matrix L[i][j] = [y_j / x_i]
(the bit of "j mod i"), i != j. Unknowns: a0, a1, b0, b1, u (n bits), v (n bits).
Solutions are returned as int bitmasks over the variable order
  a0, a1, b0, b1, u_0..u_{n-1}, v_0..v_{n-1}.
"""
from sel2 import kernel, rref, in_span


def lam(c):
    return 1 if c % 4 == 3 else 0


def mu(c):
    return 1 if c % 8 in (3, 5) else 0


def check_reciprocity(c, L):
    n = len(c)
    for i in range(n):
        for j in range(n):
            if i != j and (L[i][j] ^ L[j][i]) != lam(c[i]) * lam(c[j]):
                return False
    return True


def equations(c, L):
    """Return the list of equations, each as an int bitmask over the variables (= 0)."""
    n = len(c)
    A0, A1, B0, B1 = 0, 1, 2, 3
    U = lambda i: 4 + i
    V = lambda i: 4 + n + i
    bit = lambda k: 1 << k
    eqs = []
    for x in range(n):
        lx, mx = lam(c[x]), mu(c[x])
        e1 = 0
        e2 = 0
        for y in range(n):
            if y != x and L[x][y]:
                e1 ^= bit(U(y)) ^ bit(U(x))
                e2 ^= bit(V(y)) ^ bit(V(x))
        if lx:
            e1 ^= bit(V(x)) ^ bit(A0)
            e2 ^= bit(V(x)) ^ bit(B0)
        if mx:
            e1 ^= bit(A1)
            e2 ^= bit(U(x)) ^ bit(B1)
        eqs += [e1, e2]
    eqs.append(bit(A0) ^ bit(B0))  # (R)
    cc = 1
    for t in c:
        cc = cc * t % 8
    lu = mu_u = lv = 0
    for x in range(n):
        if lam(c[x]):
            lu ^= bit(U(x))
            lv ^= bit(V(x))
        if mu(c[x]):
            mu_u ^= bit(U(x))
    eqs.append(bit(A1))
    if cc == 1:
        eqs += [mu_u, lv ^ lu]
    elif cc == 3:
        eqs += [bit(B0) ^ lv, bit(B1) ^ mu_u]
    elif cc == 5:
        eqs += [bit(B1) ^ mu_u, lv ^ lu]
    else:
        eqs += [mu_u, bit(B0) ^ lv]
    return eqs, cc


def solve(c, L):
    """Basis of the solution space (int masks)."""
    n = len(c)
    nv = 4 + 2 * n
    eqs, _ = equations(c, L)
    # column j image = which equations contain variable j
    cols = [0] * nv
    for k, e in enumerate(eqs):
        for j in range(nv):
            if e >> j & 1:
                cols[j] |= 1 << k
    return kernel(cols, nv)


def first_coord_in(sols, n, a0, uset):
    """Is there a solution with a0, a1 = 0 and u = indicator of uset?"""
    mask = 0b11 | (((1 << n) - 1) << 4)  # a0, a1, u
    target = a0 | sum(1 << (4 + i) for i in uset)
    return in_span(rref([s & mask for s in sols]), target)


def config_of(primes):
    """Configuration of the odd squarefree d = prod(primes) via Legendre symbols."""
    from sel2 import legendre_bit
    c = [p % 8 for p in primes]
    n = len(primes)
    L = [[0 if i == j else legendre_bit(primes[j], primes[i]) for j in range(n)] for i in range(n)]
    return c, L
