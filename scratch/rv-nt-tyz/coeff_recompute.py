"""Independent recomputation of the genus-point coefficients c_n(e) modulo 2Z[i].

Abstract configuration: r "primes" (labels 0..r-1) with classes mod 8 in {1,3,5,7}, product = 5,
and an arbitrary function g: nonempty subsets -> F_2 (g(empty) = 1).

 * L(q) for q = 1, 3 (mod 8) is computed from the recursion of TYZ Lemma 2.8 mod 2 (eps = +-1 = 1):
     q = 1: sum over unordered {d1, d2}, d1 d2 = q, of L(d1) L(d2) = g(q);
     q = 3: sum over (d1, d2), d1 = 3, d2 = 1, of L(d1) L(d2) = g(q);   L(empty) = 1.
 * P(D) for D = 5, 7 is computed from the recursion of TYZ section 3.1, in F_2[i] = Z[i]/2:
     P(D) = Z(D) - sum_{D = d0 d1, d0 = 5,7, d1 = 1,3, d1 > 1} eps(d0, d1) L(d1) P(d0),
   with eps = i if (d0, d1) = (5, 3) mod 8, else 1.
 * Compared with: Lambda(q) by direct set-partition enumeration; T5a, T5b by enumeration;
   the brackets C1 = sum_{e=5} c(e) g(e), C2 = sum_{e=7} c(e) g(e) (Lemma 3.21 coefficients);
   and the alternative reading D of Proposition 3.4 (d1 = 1 admitted and distinguished).
Elements of F_2[i] are pairs (a, b) meaning a + b i.
"""
import sys
import os
import random
from functools import lru_cache
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from genus import set_partitions

ONE, I_, ZERO = (1, 0), (0, 1), (0, 0)
# Pairs (class d0, class d1) with eps = +-i. TYZ Theorem 3.3: {(5, 3)}. Override for mutation tests,
# e.g. EPS_I="" (no i at all) or EPS_I="51" (i on (5,1) steps), via the environment.
_e = os.environ.get("EPS_I", "53")
EPS_I = {(int(_e[k]), int(_e[k + 1])) for k in range(0, len(_e), 2)}


def mul(x, y):
    a, b = x
    c, d = y
    return ((a * c - b * d) % 2, (a * d + b * c) % 2)


def add(x, y):
    return ((x[0] + y[0]) % 2, (x[1] + y[1]) % 2)


def run_config(r, cls, g, check_readings=True):
    full = (1 << r) - 1

    def c8(mask):
        v = 1
        for j in range(r):
            if mask >> j & 1:
                v = v * cls[j] % 8
        return v

    def submasks(m):
        s = m
        while True:
            yield s
            if s == 0:
                return
            s = (s - 1) & m

    @lru_cache(None)
    def L(m):
        if m == 0:
            return 1
        cm = c8(m)
        assert cm in (1, 3)
        acc = 0
        if cm == 1:
            # unordered pairs {d1, d2}, both nonempty: take d2 containing the lowest bit of m
            low = m & -m
            for d2 in submasks(m):
                d1 = m ^ d2
                if d1 == 0 or d2 == 0 or not (d2 & low) or c8(d2) != 1:
                    continue
                acc += L(d1) * L(d2)
        else:
            for d2 in submasks(m):
                d1 = m ^ d2
                if d2 == 0 or d1 == 0 or c8(d2) != 1:
                    continue
                acc += L(d1) * L(d2)
        return (g[m] + acc) % 2

    @lru_cache(None)
    def P(D):
        res = {D: ONE}
        for d0 in submasks(D):
            d1 = D ^ d0
            if d1 == 0 or d0 == 0:
                continue
            if c8(d0) not in (5, 7) or c8(d1) not in (1, 3):
                continue
            if L(d1) == 0:
                continue
            eps = I_ if (c8(d0), c8(d1)) in EPS_I else ONE
            for e, c in P(d0).items():
                res[e] = add(res.get(e, ZERO), mul(eps, c))  # minus = plus mod 2
        return res

    def blocks_w(m):
        """Yield (classes, weight) over set partitions of the primes in m."""
        items = [j for j in range(r) if m >> j & 1]
        for pi in set_partitions(items):
            masks = [sum(1 << j for j in B) for B in pi]
            yield [c8(b) for b in masks], (lambda ms: __import__('math').prod(g[b] for b in ms))(masks)

    def Lam(m):
        cm = c8(m)
        tot = 0
        for cl, w in blocks_w(m):
            if cm == 1 and all(c == 1 for c in cl):
                tot += w
            if cm == 3 and cl.count(3) == 1 and cl.count(1) == len(cl) - 1:
                tot += w
        return tot % 2

    def readingD(m):  # sum (1 + k) w over partitions with at most one non-class-1 block
        cm = c8(m)
        tot = 0
        for cl, w in blocks_w(m):
            k = cl.count(1)
            if (cm == 1 and k == len(cl)) or (cm == 3 and cl.count(3) == 1 and k == len(cl) - 1):
                tot += (k + (1 if cm == 1 else 0)) * w
        return tot % 2

    out = dict(n1_fail=0, n2_fail=0, nonreal=0, br_fail=0, D_fail=0, ncoef=0)
    for q in range(1 << r):
        if c8(q) in (1, 3) and q != full:
            if L(q) != (Lam(q) if q else 1):
                out['n1_fail'] += 1
    Pn = P(full)
    C1, C2 = ZERO, ZERO
    for e in range(1, 1 << r):
        if c8(e) not in (5, 7):
            continue
        c = Pn.get(e, ZERO)
        q = full ^ e
        lam = Lam(q) if q else 1
        out['ncoef'] += 1
        if c[1]:
            out['nonreal'] += 1
        if c != (lam, 0):
            out['n2_fail'] += 1
        if check_readings and q and c[0] != readingD(q):
            out['D_fail'] += 1
        if c8(e) == 5:
            C1 = add(C1, mul(c, (g[e], 0)))
        else:
            C2 = add(C2, mul(c, (g[e], 0)))
    T5a = T5b = 0
    for cl, w in blocks_w(full):
        k = cl.count(1)
        if cl.count(5) == 1 and k == len(cl) - 1:
            T5a += w
        if cl.count(7) == 1 and cl.count(3) == 1 and k == len(cl) - 2:
            T5b += w
    if C1 != (T5a % 2, 0) or C2 != (T5b % 2, 0):
        out['br_fail'] += 1
    out['T5a'], out['T5b'] = T5a % 2, T5b % 2
    return out


def random_config(rng, r):
    while True:
        cls = [rng.choice((1, 3, 5, 7)) for _ in range(r)]
        v = 1
        for c in cls:
            v = v * c % 8
        if v == 5:
            break
    g = [1] + [rng.randint(0, 1) for _ in range(1, 1 << r)]
    return cls, g


if __name__ == "__main__":
    rng = random.Random(20261109)
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 360
    tot = dict(n1_fail=0, n2_fail=0, nonreal=0, br_fail=0, D_fail=0, ncoef=0)
    by_r, odd5b, distinct_D = {}, 0, 0
    for t in range(trials):
        r = 1 + t % 9
        cls, g = random_config(rng, r)
        o = run_config(r, cls, g)
        for k in tot:
            tot[k] += o[k]
        by_r[r] = by_r.get(r, 0) + 1
        odd5b += o['T5b']
        distinct_D += 1 if o['D_fail'] else 0
    print(f"trials {trials}, per r: {dict(sorted(by_r.items()))}")
    print(f"coefficients compared: {tot['ncoef']}")
    print(f"Lemma N1 mismatches: {tot['n1_fail']}; Lemma N2 mismatches: {tot['n2_fail']};"
          f" non-real c(e): {tot['nonreal']}; bracket (C1,C2) != (T5a,T5b): {tot['br_fail']}")
    print(f"trials with T5b odd: {odd5b}")
    print(f"reading D of Prop 3.4 disagrees with the recursion on {tot['D_fail']} coefficients"
          f" ({distinct_D} trials)")
