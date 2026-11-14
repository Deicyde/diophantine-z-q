# VERIFIED-check (pure Python, exact): for squarefree n = 5 (mod 8), F = Q(i, sqrt(q*) : q | n),
# beta = i * prod_q (1 + sqrt(q*))/2, alpha = 1 + 2 beta, and every d0 | n with d0 = 5 (mod 8):
#   Tr_{F/K_{d0}}(beta) = sqrt(-d0)   and   N_{F/K_{d0}}(alpha) = 1 + 2 sqrt(-d0)  (mod 4 O_{K_{d0}}),
# and N(alpha) * (3 - 2 sqrt(-d0)) lies in Z + 4 O_K (so its ideal class in Pic(Z + 4 O_K) is sigma_{d0}).
from fractions import Fraction
from itertools import product

def factor(n):
    fs, p = [], 2
    while p * p <= n:
        while n % p == 0:
            fs.append(p); n //= p
        p += 1
    if n > 1: fs.append(n)
    return fs

def run(n):
    qs = factor(n)
    assert len(set(qs)) == len(qs) and n % 8 == 5
    qstar = [q if q % 4 == 1 else -q for q in qs]
    r = len(qs)
    # element: dict {(a, b_1..b_r): Fraction}, monomial i^a prod sqrt(q_j*)^{b_j}
    def mul(x, y):
        z = {}
        for (ka, ca) in x.items():
            for (kb, cb) in y.items():
                c = ca * cb
                a = ka[0] + kb[0]
                if a == 2: c = -c; a = 0
                bs = []
                for j in range(r):
                    b = ka[1 + j] + kb[1 + j]
                    if b == 2: c *= qstar[j]; b = 0
                    bs.append(b)
                k = (a, *bs)
                z[k] = z.get(k, 0) + c
        return {k: v for k, v in z.items() if v != 0}
    def add(x, y):
        z = dict(x)
        for k, v in y.items(): z[k] = z.get(k, 0) + v
        return {k: v for k, v in z.items() if v != 0}
    def act(g, x):  # g = (a, b_1..b_r) sign flips
        z = {}
        for k, v in x.items():
            s = 1
            if g[0] and k[0]: s = -s
            for j in range(r):
                if g[1 + j] and k[1 + j]: s = -s
            z[k] = s * v
        return z
    one = {(0,) * (r + 1): Fraction(1)}
    def mono(a, bs): return {(a, *bs): Fraction(1)}
    beta = mono(1, [0] * r)
    for j in range(r):
        theta = {(0,) * (r + 1): Fraction(1, 2), (0, *[1 if k == j else 0 for k in range(r)]): Fraction(1, 2)}
        beta = mul(beta, theta)
    alpha = add(one, {k: 2 * v for k, v in beta.items()})
    ok = True
    for d0 in [d for d in range(1, n + 1) if n % d == 0 and d % 8 == 5]:
        S = [j for j in range(r) if d0 % qs[j] == 0]
        assert eval('*'.join(str(qstar[j]) for j in S) or '1') == d0
        H = [g for g in product([0, 1], repeat=r + 1) if (g[0] + sum(g[1 + j] for j in S)) % 2 == 0]
        tr = {}
        for g in H: tr = add(tr, act(g, beta))
        nm = one
        for g in H: nm = mul(nm, act(g, alpha))
        sq = (1, *[1 if j in S else 0 for j in range(r)])   # sqrt(-d0) = i prod_{j in S} sqrt(q_j*)
        tr_ok = (tr == {sq: Fraction(1)})
        # nm = a + b sqrt(-d0)
        keys = set(nm) - {(0,) * (r + 1), sq}
        a, b = nm.get((0,) * (r + 1), 0), nm.get(sq, 0)
        in_K = not keys and a.denominator == 1 and b.denominator == 1
        cong = in_K and (a - 1) % 4 == 0 and (b - 2) % 4 == 0
        # N(alpha) * (3 - 2 sqrt(-d0)) = (3a + 2 b d0) + (3b - 2a) sqrt(-d0)
        c0, c1 = 3 * a + 2 * b * d0, 3 * b - 2 * a
        inO4 = in_K and c1 % 4 == 0
        ok &= tr_ok and cong and inO4
        print(f"n={n} d0={d0}: Tr(beta)=sqrt(-d0): {tr_ok}; N(alpha) in O_K: {in_K}; "
              f"N(alpha)=1+2sqrt(-d0) mod 4: {cong}; N(alpha)(3-2sqrt(-d0)) in Z+4O_K: {inO4}")
    return ok

samples = [5, 13, 21, 85, 165, 205, 221 * 5 % 10000]  # 221*5 = 1105
samples = [n for n in [5, 13, 21, 85, 165, 205, 1105, 357, 1365] if n % 8 == 5]
allok = all(run(n) for n in samples)
print("ALL OK" if allok else "FAIL")
