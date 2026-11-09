"""Abstract check of the forest expansion of Smith's determinants.

Abstract data on V = [r]: bits a_ij (i != j) with a_ij + a_ji = y_i y_j, vectors y, z.
L = Laplacian (L_ij = a_ij, L_ii = sum_j a_ij).  g(B) defined by Redei/Table 1:
  y(B)=1: det L_B[B-i, B-i];  y(B)=0: det(L_B[B, B-i] | z_B).
Compares det M_1, det M_5b with set-partition sums.
"""
import random, sys, itertools
from functools import lru_cache

def det2(M):
    M = [row[:] for row in M]; n = len(M)
    for c in range(n):
        p = next((i for i in range(c, n) if M[i][c]), None)
        if p is None: return 0
        M[c], M[p] = M[p], M[c]
        for i in range(c + 1, n):
            if M[i][c]:
                M[i] = [x ^ w for x, w in zip(M[i], M[c])]
    return 1

def rand_conf(r, rng):
    y = [rng.randrange(2) for _ in range(r)]
    z = [rng.randrange(2) for _ in range(r)]
    a = [[0] * r for _ in range(r)]
    for i in range(r):
        for j in range(i + 1, r):
            a[i][j] = rng.randrange(2); a[j][i] = a[i][j] ^ (y[i] & y[j])
    return a, y, z

def lap(a, S):
    S = list(S)
    return [[(sum(a[i][k] for k in S if k != i) % 2) if i == j else a[i][j] for j in S] for i in S]

def g(a, y, z, S):
    S = list(S); L = lap(a, S)
    if sum(y[i] for i in S) % 2:
        return det2([row[1:] for row in L[1:]])
    return det2([row[1:] + [z[S[k]]] for k, row in enumerate(L)])

def cls(y, z, S):
    yy = sum(y[i] for i in S) % 2; zz = sum(z[i] for i in S) % 2
    return {(0, 0): 1, (0, 1): 5, (1, 0): 7, (1, 1): 3}[(yy, zz)]

def partitions(S):
    S = list(S)
    if not S:
        yield []; return
    first, rest = S[0], S[1:]
    for k in range(len(rest) + 1):
        for comb in itertools.combinations(rest, k):
            B = (first,) + comb
            others = [x for x in rest if x not in comb]
            for p in partitions(others):
                yield [B] + p

def partsum(a, y, z, V, want):
    """sum over partitions of V whose multiset of block classes satisfies want(list)"""
    tot = 0
    for p in partitions(V):
        cl = [cls(y, z, B) for B in p]
        if want(cl):
            prod = 1
            for B in p:
                prod &= g(a, y, z, B)
                if not prod: break
            tot ^= prod
    return tot

def M1(a, y, z, V):
    r = len(V); L = lap(a, V)
    X = [[(y[V[i]] & y[V[j]]) if i != j else 0 for j in range(r)] for i in range(r)]
    top = [X[i] + [L[j][i] for j in range(r)] for i in range(r)]
    bot = [L[i] + [z[V[i]] if j == i else 0 for j in range(r)] for i in range(r)]
    return top + bot

def bordered(M, u):
    return [row + [u[i]] for i, row in enumerate(M)] + [u + [0]]

def main(trials, rmax, seed):
    rng = random.Random(seed); bad = {}; cnt = {}
    for _ in range(trials):
        r = rng.randint(1, rmax); a, y, z = rand_conf(r, rng); V = list(range(r))
        c = cls(y, z, V); M = M1(a, y, z, V); d1 = det2(M)
        tests = {}
        # row 1 (Smith) and the forest formula: even # of blocks, all class 3
        if c == 1:
            tests['row1_smith'] = (d1, partsum(a, y, z, V, lambda cl: all(x == 1 for x in cl)))
        tests['forest_M1'] = (d1, partsum(a, y, z, V, lambda cl: len(cl) % 2 == 0 and all(x == 3 for x in cl)))
        if c == 5:
            u = [0] * r + y[:]
            d5b = det2(bordered(M, u))
            tests['row5b_smith'] = (d5b, partsum(a, y, z, V,
                lambda cl: cl.count(7) == 1 and cl.count(3) == 1 and all(x in (1, 3, 7) for x in cl)))
        for k, (l, rr) in tests.items():
            cnt[k] = cnt.get(k, 0) + 1
            if l != rr: bad[k] = bad.get(k, 0) + 1
    print('trials', trials, 'rmax', rmax, 'counts', cnt, 'mismatches', bad)

if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
