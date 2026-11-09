"""Exhaustive symbolic test of the theorem of slot-k 2.5 over abstract configurations.

Enumerates, for |P| = a, |T| = b: classes mod 8 of the primes of beta (product 7) and theta
(product 1), all symbols among P, among T and from P to T, with the reverse symbols fixed by
reciprocity, subject to (theta3) [beta/l] = 0 and (theta4) [theta/p] = 0; both signs of beta; every
choice of p0.  The slots are added symbolically as prescribed in 2.4 (q0's symbols at T either 0,
as prescribed, or arbitrary with MODE=free).  Checks with the Proposition 0 system (prop0.py) that
both configurations have dimension 3 and contain the class beta = (-1)^s prod P.
Usage: t_symbolic_exh.py a b [free]"""
import sys, itertools
from prop0 import solve_system, lam, contains_first

a, b = int(sys.argv[1]), int(sys.argv[2])
FREE = len(sys.argv) > 3 and sys.argv[3] == 'free'
CL = (1, 3, 5, 7)


def lamc(c): return 1 if c % 4 == 3 else 0


def prod8(cs):
    r = 1
    for c in cs:
        r = r * c % 8
    return r


P = ['p%d' % i for i in range(a)]
T = ['l%d' % i for i in range(b)]
pairsP = list(itertools.combinations(P, 2))
pairsT = list(itertools.combinations(T, 2))
cross = [(p, l) for p in P for l in T]
nbits = len(pairsP) + len(pairsT) + len(cross)
total = fails = 0
fail_examples = []
for cP in itertools.product(CL, repeat=a):
    if prod8(cP) != 7:
        continue
    for cT in itertools.product(CL, repeat=b):
        if prod8(cT) != 1:
            continue
        c = dict(zip(P, cP)); c.update(zip(T, cT))
        for bits in range(1 << nbits):
            L = {}
            k = 0
            for (x, y) in pairsP + pairsT:
                bx = bits >> k & 1; k += 1
                L[(x, y)] = bx                         # [y/x]
                L[(y, x)] = bx ^ (lamc(c[x]) & lamc(c[y]))
            for (p, l) in cross:
                bx = bits >> k & 1; k += 1
                L[(l, p)] = bx                         # [p/l]
                L[(p, l)] = bx ^ (lamc(c[p]) & lamc(c[l]))  # [l/p]
            # (theta4): sum_l [l/p] = 0 for every p
            if any(sum(L[(p, l)] for l in T) % 2 for p in P):
                continue
            for s in (0, 1):
                # (theta3): [beta/l] = s*lam_l + sum_p [p/l] = 0
                if any((s * lamc(c[l]) + sum(L[(l, p)] for p in P)) % 2 for l in T):
                    continue
                x = (s + 1) % 2
                for p0 in P:
                    for qfree in (range(1 << b) if FREE else [0]):
                        total += 1
                        C = dict(c); LL = dict(L)
                        C['q0'] = 3
                        tot = 0
                        for p in P:
                            if p == p0:
                                continue
                            w = (1 + lamc(c[p]) * x) % 2
                            tot ^= w
                            LL[(p, 'q0')] = w                     # [q0/p]
                        LL[(p0, 'q0')] = (x + tot) % 2
                        for i, l in enumerate(T):
                            LL[(l, 'q0')] = qfree >> i & 1          # [q0/l]
                        for y in P + T:
                            LL[('q0', y)] = LL[(y, 'q0')] ^ (lamc(c[y]) & 1)  # q0 = 3 mod 4
                        RP = []
                        for p in P:
                            if p == p0:
                                continue
                            r = 'r_' + p; C[r] = 1
                            for y in P + T + ['q0'] + RP:
                                val = 1 if y in (p, p0) else 0
                                LL[(y, r)] = val; LL[(r, y)] = val
                            RP.append(r)
                        RT = []
                        for l in T:
                            r = 'r_' + l; C[r] = 1
                            for y in P + T + ['q0'] + RP + RT:
                                val = 1 if y in (l, 'q0') else 0
                                LL[(y, r)] = val; LL[(r, y)] = val
                            RT.append(r)
                        ok = True
                        for S in (P + ['q0'] + RP + RT, P + T + ['q0'] + RP + RT):
                            Lsub = {(u, v): LL[(u, v)] for u in S for v in S if u != v}
                            dim, ker = solve_system(S, C, Lsub)
                            tgt = s
                            for i, y in enumerate(S):
                                if y in P:
                                    tgt |= 1 << (4 + i)
                            if dim != 3 or not contains_first(ker, tgt, len(S)):
                                ok = False
                        if not ok:
                            fails += 1
                            if len(fail_examples) < 5:
                                fail_examples.append((cP, cT, bits, s, p0, qfree))
print("a=%d b=%d free=%s: %d cases, %d failures %s" % (a, b, FREE, total, fails, fail_examples))
