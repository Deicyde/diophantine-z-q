"""Check, on abstract data, the exact encodings used in PropN.lean:
(a) N1 core: Lam satisfies the I2 encoding mod 2 (m = 1: pairs d = 1 mod 8, d*d < m; m = 3: d = 1 mod 8);
(b) matching: sum_{e | n, e = 7} Lam(n/e) g(e) = T5b(n), sum_{e = 5} Lam(n/e) g(e) = T5a(n).
Primes are indices with random classes mod 8 and random 'sizes' (to define d*d < m we use a
random positive real size per prime, product = size of the divisor); g is a random bit per subset.
Lam(S) = sum over set partitions of S, all blocks of class 1 or 3, at most one class-3 block."""
import random, itertools, sys, math
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 2)

def setparts(S):
    S = list(S)
    if not S: yield []; return
    a, rest = S[0], S[1:]
    for k in range(len(rest) + 1):
        for comb in itertools.combinations(rest, k):
            B = frozenset((a,) + comb)
            for p in setparts([x for x in rest if x not in comb]):
                yield [B] + p

def subsets(S):
    S = sorted(S)
    for r in range(len(S) + 1):
        for T in itertools.combinations(S, r): yield frozenset(T)

def run(r):
    pc = [random.choice([1, 3, 5, 7]) for _ in range(r)]
    sz = [math.log(random.choice([3,5,7,11,13,17,19,23,29,31,37,41,43,47])) + random.random()*1e-3 for _ in range(r)]
    cls = lambda S: math.prod(pc[p] for p in S) % 8
    size = lambda S: sum(sz[p] for p in S)
    g = {S: random.randint(0, 1) for S in subsets(range(r))}
    g[frozenset()] = 1
    def lam(S):
        t = 0
        for P in setparts(S):
            if all(cls(B) in (1, 3) for B in P) and sum(cls(B) == 3 for B in P) <= 1:
                t += math.prod(g[B] for B in P)
        return t % 2
    L = {S: lam(S) for S in subsets(range(r))}
    bad = 0
    for S in subsets(range(r)):
        if len(S) == 0: 
            bad += L[S] != 1; continue
        if cls(S) == 1:
            s = sum(L[D] * L[S - D] for D in subsets(S) if cls(D) == 1 and 2 * size(D) < size(S))
            bad += (s - g[S]) % 2 != 0
        elif cls(S) == 3:
            s = sum(L[S - D] * L[D] for D in subsets(S) if cls(D) == 1)
            bad += (s - g[S]) % 2 != 0
    N = frozenset(range(r))
    mbad = 0
    if cls(N) == 5:
        T5a = T5b = 0
        for P in setparts(N):
            cs = [cls(B) for B in P]
            w = math.prod(g[B] for B in P)
            if cs.count(5) == 1 and all(c in (1, 5) for c in cs): T5a += w
            if cs.count(7) == 1 and cs.count(3) == 1 and all(c in (1, 3, 7) for c in cs): T5b += w
        a = sum(L[N - E] * g[E] for E in subsets(N) if E and cls(E) == 5)
        b = sum(L[N - E] * g[E] for E in subsets(N) if E and cls(E) == 7)
        mbad += (a - T5a) % 2 != 0
        mbad += (b - T5b) % 2 != 0
    return bad, mbad, cls(N) == 5

tb = tm = n5 = 0; trials = 0
for r in range(0, 8):
    for _ in range(25 if r < 7 else 5):
        b, m, f = run(r); tb += b; tm += m; n5 += f; trials += 1
print(f"trials={trials}  N1-core mismatches={tb}  matching trials(n=5)={n5} mismatches={tm}")
