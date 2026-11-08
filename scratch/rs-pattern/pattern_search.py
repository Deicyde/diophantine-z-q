"""C3. Scaled-down search for the prime configurations required by 22P (catalogue-free
form) and by the difference variant, with the old primes {2, 3, 5, 7} in place of the
primes up to 324.

Residue recipe (the analogue of local_choice.py): u1 = u2 = rho mod 1680 with
rho = 1 mod 16, 3 mod 7, 1 mod 3, 1 mod 5 (rho = 241); v = 1680 * omega (v_2(v) = 4).
Then every value u_j - c v (j = 1, 2) and -(u_3 - c v)/2 (u_3 = A v - u_1 - u_2) lies in
the progression rho mod 840, i.e. is = 1 mod 8, = 3 mod 7 and prime to 3 and 5.

Sum variant: find u1, u2, v with all eighteen numbers prime and good.
Difference variant: find u, v with the numbers u - c v, c in C u (A + C), prime and good
(t1 = u / v, t2 = t1 - A).
"""
import sys, time
import numpy as np
from math import gcd, isqrt
from ntlib import two_squares, odd_part, primes_upto

RHO, STEP = 241, 840
C = [0, -15, -20, -24, -30, -60]

def good_progression(nmax):
    """Boolean array g with g[k] = (RHO + STEP k is a good prime)."""
    K = (nmax - RHO) // STEP + 1
    is_p = np.ones(K, dtype=bool)
    for q in primes_upto(isqrt(nmax) + 1):
        q = int(q)
        if STEP % q == 0:
            continue
        k0 = (-RHO) * pow(STEP, -1, q) % q
        # do not strike q itself
        start = k0 if RHO + STEP * k0 != q else k0 + q
        is_p[start::q] = False
    ks = np.nonzero(is_p)[0]
    good = np.zeros(K, dtype=bool)
    for k in ks.tolist():
        p = RHO + STEP * k
        a, b = two_squares(p)
        if odd_part(gcd(a, p + 1)) == 1:
            good[k] = True
    return good

def is_good(good, n):
    n = np.asarray(n, dtype=np.int64)
    k, r = np.divmod(n - RHO, STEP)
    ok = (r == 0) & (k >= 0) & (k < len(good))
    out = np.zeros(n.shape, dtype=bool)
    out[ok] = good[k[ok]]
    return out

def search_sum(good, A, Y, omegas):
    us = RHO + 1680 * np.arange(0, Y // 1680, dtype=np.int64)
    for om in omegas:
        v = 1680 * om
        L = us[is_good(good, us)]
        for c in C[1:]:
            L = L[is_good(good, L - c * v)]
        if len(L) < 1:
            continue
        s = (L[:, None] + L[None, :]).ravel()
        i1 = np.repeat(np.arange(len(L)), len(L)); i2 = np.tile(np.arange(len(L)), len(L))
        mask = s > (A + 61) * v
        for c in C:
            w = s - (A - c) * v            # = -(u3 - c v), even
            mask &= is_good(good, w // 2)
        hits = np.nonzero(mask)[0]
        if len(hits):
            h = hits[0]
            return int(L[i1[h]]), int(L[i2[h]]), int(v)
    return None

def search_diff(good, A, Y, omegas):
    shifts = sorted(set(C) | {A + c for c in C})
    us = RHO + 1680 * np.arange(0, Y // 1680, dtype=np.int64)
    for om in omegas:
        v = 1680 * om
        L = us
        for c in shifts:
            L = L[is_good(good, L - c * v)]
            if len(L) == 0:
                break
        if len(L):
            return int(L[0]), int(v)
    return None

if __name__ == "__main__":
    mode = sys.argv[1]
    t0 = time.time()
    NMAX = int(float(sys.argv[2])) if len(sys.argv) > 2 else int(4e10)
    good = good_progression(NMAX)
    print(f"progression sieve to {NMAX:.1e}: {good.sum()} good primes, {time.time() - t0:.0f}s", flush=True)
    sample = [0, 1, -1, 2, 5, 13, 100, -100, 1000, 12345]
    for A in sample:
        t1 = time.time()
        if mode == "sum":
            Y = NMAX // 4
            vmax = min(NMAX // (4 * (abs(A) + 61)), Y // (abs(A) + 61))
            res = search_sum(good, A, Y, range(1, vmax // 1680, 2))
        else:
            Y = NMAX // 2
            vmax = NMAX // (4 * (abs(A) + 61))
            res = search_diff(good, A, Y, range(1, vmax // 1680, 2))
        print(A, res, f"{time.time() - t1:.0f}s", flush=True)
