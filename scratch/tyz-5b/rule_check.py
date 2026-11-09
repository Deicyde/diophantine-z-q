"""Validation on actual curves C_n, n odd positive squarefree, n = 5 mod 8.

For each n:  Sel_2(C_n) by the exact descent scratch/rv-route-k/sel2cong.py (independent of the
note);  Smith/Monsky matrix M_1 from Legendre symbols;  checks
  K1  dim Sel_2 = 2 + corank M_1                                   (Lemma K)
  K2  for Selmer-minimal n: the representative (a,b) of sigma + torsion with b odd and a = 1 mod 4
      gives (S(ab), S(a)) in ker M_1                               (Lemma K)
  K3  det M_5b = chi_{-1}(|a|_odd) for every representative a      (bordered lemma + Lemma K)
  T   TYZ tau(1/2) bracket  sum_{d0=7,d1=3 (8)} g(d0) g(d1) L(n/d0d1)  with g from PARI class groups
      (independent of Redei theory) equals det M_5b   (only when omega(n) <= OMAX)
Usage: rule_check.py COUNT OMEGA_MIN OMEGA_MAX PRIME_BOUND OMAX SEED
"""
import sys, random, itertools
from functools import lru_cache
sys.path.insert(0, __file__.rsplit('/', 1)[0])
sys.path.insert(0, __file__.rsplit('/', 2)[0] + '/rv-route-k')
import sel2cong as S2
from forest_check import det2
import cypari2
pari = cypari2.Pari(); pari.allocatemem(10 ** 9)

def leg(a, p):
    a %= p
    return 0 if pow(a, (p - 1) // 2, p) == 1 else 1

def smith_M1(ps):
    r = len(ps)
    y = [1 if p % 4 == 3 else 0 for p in ps]
    z = [1 if p % 8 in (3, 5) else 0 for p in ps]
    A = [[0] * r for _ in range(r)]
    for i in range(r):
        for j in range(r):
            if i != j: A[i][j] = leg(ps[j], ps[i])
        A[i][i] = sum(A[i][j] for j in range(r) if j != i) % 2
    top = [[(A[i][j] ^ A[j][i]) if i != j else 0 for j in range(r)] + [A[j][i] for j in range(r)] for i in range(r)]
    bot = [A[i][:] + [z[i] if j == i else 0 for j in range(r)] for i in range(r)]
    return top + bot, y, z

def kernel(M):
    n = len(M); rows = [sum(M[i][j] << j for j in range(n)) for i in range(n)]
    piv = []; R = rows[:]
    # row reduce to find nullspace of M (M symmetric so row/col same)
    pivcols = []; red = []
    for row in R:
        for (pc, pr) in zip(pivcols, red):
            if row >> pc & 1: row ^= pr
        if row:
            pc = row.bit_length() - 1
            for k in range(len(red)):
                if red[k] >> pc & 1: red[k] ^= row
            pivcols.append(pc); red.append(row)
    free = [j for j in range(n) if j not in pivcols]
    basis = []
    for f in free:
        v = 1 << f
        for pc, pr in zip(pivcols, red):
            if pr >> f & 1: v |= 1 << pc
        basis.append(v)
    return basis

@lru_cache(maxsize=None)
def g_pari(d):
    D = -d if d % 4 == 3 else -4 * d
    cyc = pari.quadclassunit(D)[1]
    return 0 if any(int(c) % 4 == 0 for c in cyc) else 1

def tyz_5b(ps):
    """sum over set partitions: one block = 7, one = 3, rest = 1 (mod 8), of prod g (PARI)."""
    def parts(S):
        if not S: yield []; return
        f, rest = S[0], S[1:]
        for k in range(len(rest) + 1):
            for comb in itertools.combinations(rest, k):
                B = (f,) + comb
                for p in parts([x for x in rest if x not in comb]): yield [B] + p
    tot = 0
    for p in parts(list(ps)):
        ds = [eval('*'.join(map(str, B))) for B in p]
        cl = [d % 8 for d in ds]
        if cl.count(7) == 1 and cl.count(3) == 1 and cl.count(1) == len(cl) - 2:
            v = 1
            for d in ds:
                v &= g_pari(d)
                if not v: break
            tot ^= v
    return tot

def chi_m1_odd(mask, gens):
    """[odd part of |a| = 3 mod 4] for the class with bitmask over gens = [-1, 2, p...]"""
    return sum(1 for i, gg in enumerate(gens) if i >= 2 and mask >> i & 1 and gg % 4 == 3) % 2

def run(count, omin, omax, pb, OMAX, seed):
    rng = random.Random(seed)
    primes = [int(p) for p in pari.primes(pari.primepi(pb))][1:]
    stats = dict(n=0, minimal=0, K1=0, K2=0, K3=0, T=0, Tcount=0, det1=0)
    while stats['n'] < count:
        k = rng.randint(omin, omax); ps = sorted(rng.sample(primes, k)); n = 1
        for p in ps: n *= p
        if n % 8 != 5: continue
        stats['n'] += 1
        basis, gens = S2.selmer(n, ps)
        dimS = len(basis)
        M, y, z = smith_M1(ps); r = len(ps)
        ker = kernel(M)
        if dimS == 2 + len(ker): stats['K1'] += 1
        else: print('K1 FAIL', n, ps, dimS, len(ker))
        if dimS != 3: continue
        stats['minimal'] += 1
        # find a non-torsion class and its 4 representatives
        idx = {gg: i for i, gg in enumerate(gens)}
        tors = [(S2.vec_of(-1, gens), S2.vec_of(-n, gens)), (S2.vec_of(n, gens), S2.vec_of(2, gens))]
        tspan = {(0, 0), tors[0], tors[1], (tors[0][0] ^ tors[1][0], tors[0][1] ^ tors[1][1])}
        sig = next(v for v in basis if v not in tspan)
        reps = [(sig[0] ^ t[0], sig[1] ^ t[1]) for t in tspan]
        def bits(mask):  # u-vector over odd primes, sign bit, 2 bit
            return [mask >> (i + 2) & 1 for i in range(r)], mask & 1, mask >> 1 & 1
        good = []
        for (am, bm) in reps:
            u, a0, a1 = bits(am); v, b0, b1 = bits(bm)
            lam_u = sum(u[i] * y[i] for i in range(r)) % 2
            if b1 == 0 and a0 == lam_u: good.append((u, v))
        ok2 = len(good) == 1
        if ok2:
            u, v = good[0]
            vec = sum(((u[i] ^ v[i]) << i) | (u[i] << (r + i)) for i in range(r))
            Mv = [sum(M[i][j] & (vec >> j & 1) for j in range(2 * r)) % 2 for i in range(2 * r)]
            ok2 = not any(Mv) and len(ker) == 1 and ker[0] == vec
        stats['K2'] += ok2
        if not ok2: print('K2 FAIL', n, ps)
        Mb = [row + [0] * r + [y[i - r] if i >= r else 0] for i, row in enumerate(M)]
        Mb = [Mb[i][:2 * r] + [y[i - r] if i >= r else 0] for i in range(2 * r)] + [[0] * r + y + [0]]
        d5 = det2(Mb); stats['det1'] += d5
        rule = {chi_m1_odd(am, gens) for (am, bm) in reps}
        ok3 = rule == {d5}
        stats['K3'] += ok3
        if not ok3: print('K3 FAIL', n, ps, rule, d5)
        if r <= OMAX:
            stats['Tcount'] += 1
            t = tyz_5b(ps)
            stats['T'] += (t == d5)
            if t != d5: print('T FAIL', n, ps, t, d5)
    print('seed', seed, 'omega', omin, omax, 'primes <', pb, stats)

if __name__ == '__main__':
    run(*map(int, sys.argv[1:7]))
