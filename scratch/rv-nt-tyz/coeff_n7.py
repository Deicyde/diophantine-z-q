"""n = 7 (mod 8) remark of nt-tyz 4.4: c_n(e) = i*Lambda(n/e) for e = 5, Lambda(n/e) for e = 7 (mod 2Z[i]).
Reuses the recursion code of coeff_recompute.py by patching the target class."""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import coeff_recompute as C

def cfg(rng, r):
    while True:
        cls = [rng.choice((1, 3, 5, 7)) for _ in range(r)]
        v = 1
        for c in cls: v = v * c % 8
        if v == 7: return cls, [1] + [rng.randint(0, 1) for _ in range(1, 1 << r)]

rng = random.Random(77)
bad = tot = 0
for t in range(120):
    r = 1 + t % 8
    cls, g = cfg(rng, r)
    # call internals: build closures by running run_config's body pieces
    full = (1 << r) - 1
    o = {}
    # reuse run_config with a trick: it reports n2_fail against (Lam, 0); count expected failures for e = 5
    import types
    src = C.run_config
    res = []
    def c8(m):
        v = 1
        for j in range(r):
            if m >> j & 1: v = v * cls[j] % 8
        return v
    from functools import lru_cache
    from genus import set_partitions
    import math
    def subm(m):
        s = m
        while True:
            yield s
            if s == 0: return
            s = (s - 1) & m
    @lru_cache(None)
    def L(m):
        if m == 0: return 1
        cm = c8(m); acc = 0; low = m & -m
        for d2 in subm(m):
            d1 = m ^ d2
            if d1 == 0 or d2 == 0 or c8(d2) != 1: continue
            if cm == 1 and not (d2 & low): continue
            acc += L(d1) * L(d2)
        return (g[m] + acc) % 2
    @lru_cache(None)
    def P(D):
        res = {D: C.ONE}
        for d0 in subm(D):
            d1 = D ^ d0
            if not d0 or not d1 or c8(d0) not in (5, 7) or c8(d1) not in (1, 3) or not L(d1): continue
            eps = C.I_ if (c8(d0), c8(d1)) == (5, 3) else C.ONE
            for e, c in P(d0).items(): res[e] = C.add(res.get(e, C.ZERO), C.mul(eps, c))
        return res
    def Lam(m):
        if m == 0: return 1
        items = [j for j in range(r) if m >> j & 1]; cm = c8(m); s = 0
        for pi in set_partitions(items):
            ms = [sum(1 << j for j in B) for B in pi]; cl = [c8(b) for b in ms]
            if cl.count(1) == len(cl) - (0 if cm == 1 else 1) and (cm == 1 or cl.count(3) == 1):
                s += math.prod(g[b] for b in ms)
        return s % 2
    Pn = P(full)
    for e in range(1, 1 << r):
        if c8(e) not in (5, 7): continue
        lam = Lam(full ^ e); tot += 1
        want = (0, lam) if c8(e) == 5 else (lam, 0)
        bad += Pn.get(e, C.ZERO) != want
print("n = 7 configurations: 120; coefficients:", tot, "; mismatches with i^[e=5] Lambda(n/e):", bad)
