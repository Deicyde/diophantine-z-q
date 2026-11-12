"""Check Lemma N2 in the L-form: c_n(e) = L(n/e) mod 2Z[i] (e = n: c = 1), for n = 5 mod 8,
with arbitrary integer L (no Lemma 2.8 / N1 needed) and eps = +-1 off (5,3), +-i at (5,3).
Abstract primes: a squarefree number is a frozenset of prime indices, class = product of prime
classes mod 8. Also run the variant where eps at (5,3) is a random unit (mixed classes)."""
import random, itertools, sys
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)

def cls(S, pc):
    c = 1
    for p in S: c = c * pc[p] % 8
    return c

def subsets(S):
    S = sorted(S)
    for r in range(len(S) + 1):
        for T in itertools.combinations(S, r):
            yield frozenset(T)

def trial(r, mixed):
    while True:
        pc = [random.choice([1, 3, 5, 7]) for _ in range(r)]
        N = frozenset(range(r))
        if cls(N, pc) == 5: break
    L = {S: random.randint(-5, 5) for S in subsets(N)}
    eps = {}
    def ep(d0, d1):
        k = (d0, d1)
        if k not in eps:
            if cls(d0, pc) == 5 and cls(d1, pc) == 3:
                eps[k] = random.choice([1j, -1j, 1, -1] if mixed else [1j, -1j])
            else:
                eps[k] = random.choice([1, -1])
        return eps[k]
    # c[d] : dict e -> complex (Gaussian integer), P(d) = sum c[d][e] Z(e)
    ds = [S for S in subsets(N) if cls(S, pc) in (5, 7)]
    ds.sort(key=len)
    c = {}
    for d in ds:
        cd = {d: 1}
        for d1 in subsets(d):
            if len(d1) == 0 or cls(d1, pc) not in (1, 3): continue
            d0 = d - d1
            for e, v in c[d0].items():
                cd[e] = cd.get(e, 0) - ep(d0, d1) * L[d1] * v
        c[d] = cd
    bad = 0
    for e, v in c[N].items():
        target = 1 if e == N else L[N - e]
        diff = v - target
        if round(diff.real) % 2 or round(diff.imag) % 2: bad += 1
    return bad

for mixed in (False, True):
    tot = 0; trials = 0
    for r in range(1, 8):
        for _ in range(30 if r < 7 else 10):
            tot += trial(r, mixed); trials += 1
    print(f"mixed={mixed}: trials={trials} mismatched coefficients={tot}")
