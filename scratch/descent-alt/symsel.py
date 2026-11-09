"""Symbolic 2-Selmer groups of C_d : y^2 = x^3 - d^2 x for odd squarefree d > 0, from the
pairwise Legendre data of the primes of d alone.

Unknowns: a = (-1)^{a0} 2^{a1} prod p^{u_p},  b = (-1)^{b0} 2^{b1} prod p^{v_p}  (Kummer coordinates
(x, x - d)).  With L_ij = [p_j/p_i] (i != j), A = L + diag(L 1), lam = [-1/p], mu = [2/p]:
  odd p | d :  A u + D_lam v = a0 lam + a1 mu,   D_mu u + (A + D_lam) v = b0 lam + b1 mu
  real      :  a0 = b0
  2-adic    :  d = 1 (8): a1 = 0, mu.u = 0, lam.v = lam.u      (with a0 = b0)
               d = 3 (8): a1 = 0, b0 = lam.v, b1 = mu.u
               d = 5 (8): a1 = 0, b1 = mu.u, lam.v = lam.u
               d = 7 (8): a1 = 0, mu.u = 0, b0 = lam.v
Data: a 'config' is (dmod8, lam list, mu list, L matrix as list of lists).
"""


def legbit(a, p):
    a %= p
    return 0 if pow(a, (p - 1) // 2, p) == 1 else 1


def config_of(primes):
    k = len(primes)
    L = [[0 if i == j else legbit(primes[j], primes[i]) for j in range(k)] for i in range(k)]
    lam = [legbit(-1, p) for p in primes]
    mu = [legbit(2, p) for p in primes]
    d = 1
    for p in primes:
        d *= p
    return (d % 8, lam, mu, L)


def equations(cfg):
    """Rows as bitmasks over the unknown vector  [a0, a1, b0, b1, u_0..u_{k-1}, v_0..v_{k-1}]."""
    dm, lam, mu, L = cfg
    k = len(lam)
    A0, A1, B0, B1 = 1, 2, 4, 8
    U = lambda i: 1 << (4 + i)
    V = lambda i: 1 << (4 + k + i)
    rows = []
    for i in range(k):
        Ai = [L[i][j] for j in range(k)]
        Ai[i] = sum(L[i]) % 2
        r = 0
        for j in range(k):
            if Ai[j]: r ^= U(j)
        if lam[i]: r ^= V(i) ^ A0
        if mu[i]: r ^= A1
        rows.append(r)
        r = 0
        if mu[i]: r ^= U(i)
        for j in range(k):
            if Ai[j] ^ (lam[i] if i == j else 0): r ^= V(j)
        if lam[i]: r ^= B0
        if mu[i]: r ^= B1
        rows.append(r)
    rows.append(A0 ^ B0)
    rows.append(A1)
    lu = 0; lv = 0; mu_u = 0
    for i in range(k):
        if lam[i]: lu ^= U(i); lv ^= V(i)
        if mu[i]: mu_u ^= U(i)
    if dm == 1:
        rows += [mu_u, lu ^ lv]
    elif dm == 3:
        rows += [B0 ^ lv, B1 ^ mu_u]
    elif dm == 5:
        rows += [B1 ^ mu_u, lu ^ lv]
    elif dm == 7:
        rows += [mu_u, B0 ^ lv]
    return rows, 4 + 2 * k


def kernel(rows, n):
    """Basis of {x in F_2^n : r.x = 0 for all rows}."""
    piv = {}
    for r in rows:
        for c, pr in piv.items():
            if r >> c & 1:
                r ^= pr
        if r:
            c = r.bit_length() - 1
            for c2 in list(piv):
                if piv[c2] >> c & 1:
                    piv[c2] ^= r
            piv[c] = r
    free = [c for c in range(n) if c not in piv]
    basis = []
    for f in free:
        x = 1 << f
        for c, pr in piv.items():
            # pr has leading bit c; x_c = sum of pr's other bits in x
            if bin(pr & x & ~(1 << c)).count("1") % 2:
                x |= 1 << c
        basis.append(x)
    return basis


def selmer_dim(cfg):
    rows, n = equations(cfg)
    return len(kernel(rows, n))


def has_first(cfg, umask, a0=0):
    """Is the class a = (-1)^{a0} prod_{i in umask} p_i a first coordinate of Sel_2?"""
    rows, n = equations(cfg)
    k = len(cfg[1])
    basis = kernel(rows, n)
    target = (a0 & 1)
    for i in range(k):
        if umask >> i & 1:
            target |= 1 << (4 + i)
    proj = (1 << (4 + k)) - 1 ^ 4 ^ 8  # a0, a1, u bits
    sp = {}
    for x in basis:
        y = x & proj
        for c in sorted(sp, reverse=True):
            if y >> c & 1: y ^= sp[c]
        if y: sp[y.bit_length() - 1] = y
    y = target
    for c in sorted(sp, reverse=True):
        if y >> c & 1: y ^= sp[c]
    return y == 0
