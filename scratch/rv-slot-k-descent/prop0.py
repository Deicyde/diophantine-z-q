"""The linear system of Proposition 0, as derived in log.md step 2 (own implementation).

Unknown layout matches sel2.py: a-part bits 0..g-1 on gens (-1, 2, p_1..p_k), b-part bits g..2g-1.
So a0 = bit 0, a1 = bit 1, u_i = bit 2+i, b0 = bit g, b1 = bit g+1, v_i = bit g+2+i.
"""
import gmpy2

from sel2 import kernel


def sym(y, p):
    """[y/p] in F_2 for an odd prime p not dividing y."""
    return 0 if gmpy2.legendre(y % p, p) == 1 else 1


def prop0_rows(d, primes):
    k = len(primes)
    g = k + 2
    A0, A1, B0, B1 = 0, 1, g, g + 1
    U = lambda i: 2 + i
    V = lambda i: g + 2 + i
    lam = [sym(-1, p) for p in primes]
    mu = [sym(2, p) for p in primes]
    L = [[0 if i == j else sym(primes[j], primes[i]) for j in range(k)] for i in range(k)]
    rows = []
    for i in range(k):
        # E1_i: sum_j L_ij (u_j + u_i) + lam_i v_i + a0 lam_i + a1 mu_i = 0
        r = 0
        for j in range(k):
            if L[i][j]:
                r ^= (1 << U(j)) ^ (1 << U(i))
        if lam[i]:
            r ^= (1 << V(i)) ^ (1 << A0)
        if mu[i]:
            r ^= 1 << A1
        rows.append(r)
        # E2_i: mu_i u_i + sum_j L_ij (v_j + v_i) + lam_i v_i + b0 lam_i + b1 mu_i = 0
        r = 0
        if mu[i]:
            r ^= (1 << U(i)) ^ (1 << B1)
        for j in range(k):
            if L[i][j]:
                r ^= (1 << V(j)) ^ (1 << V(i))
        if lam[i]:
            r ^= (1 << V(i)) ^ (1 << B0)
        rows.append(r)
    rows.append((1 << A0) ^ (1 << B0))  # real place
    lu = 0; mu_u = 0; lv = 0; mv = 0
    for i in range(k):
        if lam[i]:
            lu ^= 1 << U(i); lv ^= 1 << V(i)
        if mu[i]:
            mu_u ^= 1 << U(i)
    c = d % 8
    rows.append(1 << A1)
    if c == 1:
        rows += [mu_u, lu ^ lv]
    elif c == 3:
        rows += [(1 << B0) ^ lv, (1 << B1) ^ mu_u]
    elif c == 5:
        rows += [(1 << B1) ^ mu_u, lu ^ lv]
    elif c == 7:
        rows += [mu_u, (1 << B0) ^ lv]
    return rows


def prop0_selmer(d, primes):
    gens = [-1, 2] + list(primes)
    return gens, kernel(prop0_rows(d, primes), 2 * len(gens))
