"""Independent abstract check of Lemmas N1, N2 and the bracket identification (nt-tyz 4.3-4.4).
Primes are abstract: each has a class in {1,3,5,7} (mod 8), product of classes = 5 (mod 8).
g: random bit on nonempty subsets. Gaussian integers as (re, im) ints.
- L(m) for m = 1,3: defined by I2 taken modulo 2 (Lemma 2.8 + Prop 2.3), with random sign eps=+-1
  and a random EVEN perturbation to model "holds only as a congruence"; then reduced mod 2.
- Lambda(m): set partitions, one class-3 block if m=3, rest class 1.
- c_n(e): exact unwinding in Z[i] of P(D) = Z(D) - sum eps(D/q, q) L(q) P(D/q), q>1, q = 1,3,
  D/q = 5,7, with eps(d0,d1) a random unit, = +-i iff (d0,d1) = (5,3), else +-1.
  Random integer lift of L(q) with the computed parity.
Checks: c_n(e) = Lambda(n/e) mod 2(Z[i]); a = sum_{e=5} l_e g(e) = T5a; N = sum_{e=7} l_e g(e) = T5b,
with T5a, T5b computed directly as set-partition sums.
Also checks the alternative (wrong) readings fail, to show the test has teeth."""
import random, sys
from functools import lru_cache

def run(r, rng):
    while True:
        cls = [rng.choice([1, 3, 5, 7]) for _ in range(r)]
        p = 1
        for c in cls: p = p * c % 8
        if p == 5: break
    full = (1 << r) - 1
    g = {S: rng.randint(0, 1) for S in range(1, full + 1)}
    def C(S):
        v = 1
        for i in range(r):
            if S >> i & 1: v = v * cls[i] % 8
        return v
    def subsets(S):
        T = S
        while True:
            yield T
            if T == 0: break
            T = (T - 1) & S
    # set partitions of S as lists of blocks
    @lru_cache(None)
    def partitions(S):
        if S == 0: return [()]
        low = S & -S
        rest = S ^ low
        out = []
        for T in subsets(rest):
            B = T | low
            for p in partitions(S ^ B):
                out.append((B,) + p)
        return out
    def w(pi):
        v = 1
        for B in pi: v &= g[B]
        return v
    def Lam(S):  # S class 1 or 3
        tot = 0
        for pi in partitions(S):
            cs = [C(B) for B in pi]
            if C(S) == 1 and all(c == 1 for c in cs): tot ^= w(pi)
            if C(S) == 3 and cs.count(3) == 1 and all(c in (1, 3) for c in cs): tot ^= w(pi)
        return tot
    # L via I2 mod 2, model integer values with signs and even error
    Lint = {0: 1}
    order = sorted(range(1, full + 1), key=lambda S: bin(S).count('1'))
    for S in order:
        if C(S) not in (1, 3): continue
        # sum_{S = D1 D2, D2 = 1 (8)} eps L(D1) L(D2) = Q(S) = g(S) mod 2 ; unordered for class 1
        acc = 0
        seen = set()
        for D2 in subsets(S):
            D1 = S ^ D2
            if C(D2) != 1: continue
            if D2 == 0: continue  # the term L(S) L(1): solved for
            key = frozenset((D1, D2))
            if C(S) == 1:
                if D1 == 0 or key in seen: continue  # D1 = 0 is the same pair {1, S}
                seen.add(key)
            acc += rng.choice([1, -1]) * Lint[D1] * Lint[D2]
        Q = g[S] + 2 * rng.randint(-3, 3)  # Q(S) only known = g(S) mod 2
        eps0 = rng.choice([1, -1])
        Lint[S] = eps0 * (Q - acc) + 2 * rng.randint(-2, 2)  # even error: congruence only
    bad = 0
    for S in order:
        if C(S) in (1, 3) and Lint[S] % 2 != Lam(S): bad += 1
    # eps units
    def unit(z):  # random +-z
        s = rng.choice([1, -1]); return (s * z[0], s * z[1])
    epsd = {}
    def eps(d0, d1):
        k = (d0, d1)
        if k not in epsd:
            epsd[k] = unit((0, 1)) if (C(d0), C(d1)) in IPAIRS else unit((1, 0))
        return epsd[k]
    def mul(a, b): return (a[0]*b[0] - a[1]*b[1], a[0]*b[1] + a[1]*b[0])
    @lru_cache(None)
    def P(D):  # dict e -> c in Z[i]
        res = {D: (1, 0)}
        for q in subsets(D):
            if q == 0 or C(q) not in (1, 3): continue
            d0 = D ^ q
            if C(d0) not in (5, 7): continue
            coef = mul(eps(d0, q), (Lint[q], 0))
            for e, c in P(d0).items():
                m = mul(coef, c)
                o = res.get(e, (0, 0))
                res[e] = (o[0] - m[0], o[1] - m[1])
        return res
    c = P(full)
    for e in subsets(full):
        if C(e) not in (5, 7): continue
        ce = c.get(e, (0, 0))
        if ce[0] % 2 != Lam(full ^ e) or ce[1] % 2 != 0: bad += 1
    # brackets
    a = sum(g[e] * (c.get(e, (0, 0))[0] % 2) for e in subsets(full) if e and C(e) == 5) % 2
    N = sum(g[e] * (c.get(e, (0, 0))[0] % 2) for e in subsets(full) if e and C(e) == 7) % 2
    T5a = T5b = 0
    for pi in partitions(full):
        cs = sorted(C(B) for B in pi)
        if cs.count(5) == 1 and all(x in (1, 5) for x in cs): T5a ^= w(pi)
        if cs.count(7) == 1 and cs.count(3) == 1 and all(x in (1, 3, 7) for x in cs): T5b ^= w(pi)
    if a != T5a or N != T5b: bad += 1
    # teeth: ordered-pair reading of I2 for class 1 / distinguished-d0 reading of Theorem 1.1
    alt = 0
    for S in order:
        if C(S) == 1:
            cnt = 0
            for pi in partitions(S):
                if all(C(B) == 1 for B in pi): cnt ^= (len(pi) % 2) & w(pi)
            if cnt != Lam(S): alt += 1
    return bad, T5a, T5b, alt

rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
IPAIRS = eval(sys.argv[2]) if len(sys.argv) > 2 else {(5, 3)}
tot_bad = 0; stats = {}; alts = 0
trials = 0
for r in range(1, int(sys.argv[3]) if len(sys.argv) > 3 else 10):
    nt = 60 if r <= 7 else (25 if r == 8 else 8)
    for _ in range(nt):
        b, t5a, t5b, alt = run(r, rng)
        tot_bad += b; trials += 1; alts += (alt > 0)
        stats[(t5a, t5b)] = stats.get((t5a, t5b), 0) + 1
    print("r", r, "done; cumulative mismatches", tot_bad, flush=True)
print("trials", trials, "mismatches", tot_bad, "(T5a,T5b) distribution", stats,
      "trials where b(pi)-reading differs from Lambda:", alts)
