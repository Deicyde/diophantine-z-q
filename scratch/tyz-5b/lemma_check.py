"""Checks of the individual lemmas of docs/research/tyz-5b.md on abstract data.

  kappa_sum : kappa_i(B) + kappa_j(B) = sum over 2-forests rooted at {i,j} of c(T_i), c = column sums
  forest_F  : all-minors forest lemma over F_2 (brute-force enumeration of forests, r <= 6)
  R1        : L(S) = E3(S) for class-1 S (sum over class-1 partitions = over class-3 partitions)
  M5b       : det M_5b = sum over partitions with one class-7 block, all others class 3
  row5b     : Smith row 5b (TYZ tau(1/2) bracket with Redei g) = det M_5b
Usage: lemma_check.py TRIALS RMAX SEED
"""
import sys, random, itertools
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from forest_check import det2, rand_conf, lap, g, cls, partsum, M1, bordered

def minor(M, rows, cols):
    return [[M[i][j] for j in cols] for i in rows]

def forests(a, V, roots):
    """yield (f, weight) for acyclic f: V - roots -> V with f(i) != i"""
    dom = [i for i in V if i not in roots]
    for img in itertools.product(V, repeat=len(dom)):
        f = dict(zip(dom, img))
        if any(f[i] == i for i in dom): continue
        w = 1
        for i in dom: w &= a[i][f[i]]
        if not w: continue
        ok = True
        for i in dom:          # acyclic: iterate to a root
            x, seen = i, 0
            while x in f and seen <= len(V):
                x = f[x]; seen += 1
            if x in f: ok = False; break
        if ok: yield f

def root_of(f, i):
    while i in f: i = f[i]
    return i

def main(trials, rmax, seed):
    rng = random.Random(seed); cnt = {}; bad = {}
    def rec(k, ok):
        cnt[k] = cnt.get(k, 0) + 1
        if not ok: bad[k] = bad.get(k, 0) + 1
    for _ in range(trials):
        r = rng.randint(1, rmax); a, y, z = rand_conf(r, rng); V = list(range(r))
        L = lap(a, V)
        if r <= 6:
            # forest lemma: random F, W of equal size
            m = rng.randint(1, r); F = rng.sample(V, m); W = rng.sample(V, m)
            lhs = det2(minor(L, [i for i in V if i not in F], [j for j in V if j not in W]))
            rhs = 0
            for f in forests(a, V, set(F)):
                trees = {}
                for v in V: trees.setdefault(root_of(f, v), []).append(v)
                if all(sum(1 for v in T if v in W) == 1 for T in trees.values()): rhs ^= 1
            rec('forest_F', lhs == rhs)
            # kappa sum
            if r >= 2:
                i, j = rng.sample(V, 2)
                ki = det2(minor(L, [v for v in V if v != i], [v for v in V if v != i]))
                kj = det2(minor(L, [v for v in V if v != j], [v for v in V if v != j]))
                c = [sum(L[u][v] for u in V) % 2 for v in V]
                s = 0
                for f in forests(a, V, {i, j}):
                    s ^= sum(c[v] for v in V if root_of(f, v) == i) % 2
                rec('kappa_sum', (ki ^ kj) == s)
        c = cls(y, z, V)
        if c == 1:
            rec('R1', partsum(a, y, z, V, lambda cl: all(x == 1 for x in cl)) ==
                partsum(a, y, z, V, lambda cl: all(x == 3 for x in cl)))
        if c == 5:
            d5 = det2(bordered(M1(a, y, z, V), [0] * r + y[:]))
            rec('M5b', d5 == partsum(a, y, z, V, lambda cl: cl.count(7) == 1 and cl.count(3) == len(cl) - 1))
            rec('row5b', d5 == partsum(a, y, z, V,
                lambda cl: cl.count(7) == 1 and cl.count(3) == 1 and cl.count(1) == len(cl) - 2))
    print('trials', trials, 'rmax', rmax, 'seed', seed, 'counts', cnt, 'mismatches', bad)

if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
