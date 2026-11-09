"""Independent helpers: g(d) = #2Cl(Q(sqrt(-d))) by two exact methods, set partitions, genus sums.

Method 1 (forms): h = number of reduced forms of discriminant D, #Cl[2] = number of reduced
ambiguous forms (b = 0, b = a or a = c); g = h / #Cl[2].
Method 2 (Redei): parity of g is (-1)^{r4}, r4 = t - 1 - rank_F2(Redei matrix).
"""
from math import isqrt, gcd
from itertools import combinations


def primes_of(m):
    ps, p = [], 2
    while p * p <= m:
        if m % p == 0:
            ps.append(p)
            m //= p
            assert m % p != 0, "not squarefree"
        p += 1
    if m > 1:
        ps.append(m)
    return ps


def disc(d):
    return -d if d % 4 == 3 else -4 * d


def reduced_forms(D):
    assert D < 0 and D % 4 in (0, 1)
    out = []
    a = 1
    while 3 * a * a <= -D:
        for b in range(-a + 1, a + 1):
            if (b * b - D) % (4 * a):
                continue
            c = (b * b - D) // (4 * a)
            if c < a or (c == a and b < 0):
                continue
            if gcd(gcd(a, abs(b)), c) != 1:
                continue
            out.append((a, b, c))
        a += 1
    return out


def g_forms(d):
    if d == 1:
        return 1
    fs = reduced_forms(disc(d))
    amb = [f for f in fs if f[1] == 0 or f[1] == f[0] or f[0] == f[2]]
    assert len(fs) % len(amb) == 0
    return len(fs) // len(amb)


def kron(a, n):
    """Kronecker symbol (a/n) for n a positive prime."""
    if n == 2:
        if a % 2 == 0:
            return 0
        return 1 if a % 8 in (1, 7) else -1
    r = pow(a % n, (n - 1) // 2, n)
    return 0 if r == 0 else (1 if r == 1 else -1)


def rank_f2(rows):
    rows = [r for r in rows]
    rk, ncol = 0, (len(rows[0]) if rows else 0)
    for c in range(ncol):
        piv = next((i for i in range(rk, len(rows)) if rows[i][c]), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        for i in range(len(rows)):
            if i != rk and rows[i][c]:
                rows[i] = [x ^ y for x, y in zip(rows[i], rows[rk])]
        rk += 1
    return rk


def prime_discs(d):
    """Prime discriminants whose product is disc(d) (d odd squarefree)."""
    D = disc(d)
    pd = [(-1) ** ((p - 1) // 2) * p for p in primes_of(d)]
    rest = D
    for x in pd:
        rest //= x
    if rest != 1:
        assert rest in (-4, 8, -8)
        pd.append(rest)
    return pd


def g_redei_parity(d):
    if d == 1:
        return 1
    pd = prime_discs(d)
    t = len(pd)
    ps = [abs(x) if abs(x) % 2 else 2 for x in pd]
    R = [[0] * t for _ in range(t)]
    for i in range(t):
        for j in range(t):
            if i != j:
                R[i][j] = 1 if kron(pd[j], ps[i]) == -1 else 0
        R[i][i] = sum(R[i][j] for j in range(t) if j != i) % 2
    r4 = t - 1 - rank_f2(R)
    return 1 if r4 == 0 else 0


def set_partitions(items):
    items = list(items)
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for p in set_partitions(rest):
        yield [[first]] + p
        for k in range(len(p)):
            yield p[:k] + [[first] + p[k]] + p[k + 1:]


def prod(xs):
    r = 1
    for x in xs:
        r *= x
    return r
