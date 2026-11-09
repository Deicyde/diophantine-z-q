"""Which conditions of slot-k 2.4 are load-bearing?  Random abstract data satisfying (theta1)-(theta4)
(classes, symbols, reciprocity), slots added symbolically; one family of prescribed symbols is
replaced by random bits (variant), and we count how often the theorem's conclusion fails.
Usage: t_variants.py variant trials seed
variants: none, q0P (q0 at P\\{p0}), q0T (q0 at T), rpT, rpq0, rpP (r_p at other P), rpR (r_p at
earlier r_p), rlP, rlT (r_l at other T), rlR (r_l at R_P and earlier r_l), q0mod8 (q0 = 7 mod 8),
sign (x = s)."""
import sys, random
from prop0 import solve_system, contains_first

var, N, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
rng = random.Random(seed)
CL = (1, 3, 5, 7)
def lamc(c): return 1 if c % 4 == 3 else 0
def bit(name, default):
    return rng.randint(0, 1) if var == name else default

fails = 0; fails_detail = {}; corr = {}
for trial in range(N):
    a = rng.randint(1, 6); b = rng.randint(0, 5)
    while True:
        cP = [rng.choice(CL) for _ in range(a)]
        cT = [rng.choice(CL) for _ in range(b)]
        pr = 1
        for c in cP: pr = pr * c % 8
        pt = 1
        for c in cT: pt = pt * c % 8
        if pr == 7 and pt == 1: break
    P = ['p%d' % i for i in range(a)]; T = ['l%d' % i for i in range(b)]
    C = dict(zip(P, cP)); C.update(zip(T, cT))
    L = {}
    for grp in (P, T):
        for i in range(len(grp)):
            for j in range(i + 1, len(grp)):
                x, y = grp[i], grp[j]; bx = rng.randint(0, 1)
                L[(x, y)] = bx; L[(y, x)] = bx ^ (lamc(C[x]) & lamc(C[y]))
    s = rng.randint(0, 1)
    if b:
        M = [[rng.randint(0, 1) for _ in range(b)] for _ in range(a)]   # M[p][l] = [p/l]
        lamT = sum(lamc(C[l]) for l in T) % 2
        for i in range(a - 1):
            M[i][b - 1] = (lamc(C[P[i]]) * lamT + sum(M[i][:b - 1])) % 2
        for j in range(b):
            M[a - 1][j] = (s * lamc(C[T[j]]) + sum(M[i][j] for i in range(a - 1))) % 2
        for i, p in enumerate(P):
            for j, l in enumerate(T):
                L[(l, p)] = M[i][j]; L[(p, l)] = M[i][j] ^ (lamc(C[p]) & lamc(C[l]))
        assert all(sum(L[(p, l)] for l in T) % 2 == 0 for p in P)                       # theta4
        assert all((s * lamc(C[l]) + sum(L[(l, p)] for p in P)) % 2 == 0 for l in T)     # theta3
    x = s if var == 'sign' else (s + 1) % 2
    p0 = rng.choice(P)
    C['q0'] = 7 if var == 'q0mod8' else 3
    tot = 0
    for p in P:
        if p == p0: continue
        w = bit('q0P', (1 + lamc(C[p]) * x) % 2); tot ^= w
        L[(p, 'q0')] = w
    L[(p0, 'q0')] = (x + tot) % 2
    for l in T:
        L[(l, 'q0')] = bit('q0T', 0)
    for y in P + T:
        L[('q0', y)] = L[(y, 'q0')] ^ (lamc(C[y]) & lamc(C['q0']))
    RP = []
    for p in P:
        if p == p0: continue
        r = 'r_' + p; C[r] = 1
        for y in P + T + ['q0'] + RP:
            if y in (p, p0): val = 1
            elif y in T: val = bit('rpT', 0)
            elif y == 'q0': val = bit('rpq0', 0)
            elif y in P: val = bit('rpP', 0)
            else: val = bit('rpR', 0)
            L[(y, r)] = val; L[(r, y)] = val
        RP.append(r)
    RT = []
    for l in T:
        r = 'r_' + l; C[r] = 1
        for y in P + T + ['q0'] + RP + RT:
            if y in (l, 'q0'): val = 1
            elif y in P: val = bit('rlP', 0)
            elif y in T: val = bit('rlT', 0)
            else: val = bit('rlR', 0)
            L[(y, r)] = val; L[(r, y)] = val
        RT.append(r)
    bad = []
    for name, S in (('C1', P + ['q0'] + RP + RT), ('C2', P + T + ['q0'] + RP + RT)):
        Ls = {(u, v): L[(u, v)] for u in S for v in S if u != v}
        dim, ker = solve_system(S, C, Ls)
        tgt = s
        for i, y in enumerate(S):
            if y in P: tgt |= 1 << (4 + i)
        if dim != 3: bad.append(name + ':dim%d' % dim)
        elif not contains_first(ker, tgt, len(S)): bad.append(name + ':nobeta')
    has3 = any(lamc(C[l]) for l in T)
    corr[(bool(bad), has3)] = corr.get((bool(bad), has3), 0) + 1
    if bad:
        fails += 1
        k = ','.join(bad); fails_detail[k] = fails_detail.get(k, 0) + 1
print("variant %-7s trials %d failures %d %s" % (var, N, fails, fails_detail))
if var == 'sign':
    print("  (failed, theta has a prime = 3 mod 4) counts:", corr)
