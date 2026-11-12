"""Shared helpers for rv-tyz-inputs numerics (independent of scratch/rv-prop-n/tyzlib.py).

calL(d) for odd squarefree d (TYZ L338-353):
  calL(d)^2 = L(E_d,1) / (2^{2k-3} Omega_d)            (ord 0; k = number of odd prime factors, a(d) = 1)
  calL(d)^2 = L'(E_d,1) / (2^{2k-3} Omega_d R_d)       (ord 1; R_d = 2 * NT height of a generator)
  Omega_d = (2/sqrt d) * int_1^oo dx/sqrt(x^3-x);  E_d : d y^2 = x^3 - x  ~  y^2 = x^3 - d^2 x.
g(d) = #2Cl(Q(sqrt -d)) mod 2, from Redei's 4-rank formula (unconditional), cross-checked with quadclassunit.
"""
import itertools
import cypari2
pari = cypari2.Pari()
pari.allocatemem(2 * 10**9)
pari.set_real_precision(38)

OMEGA_INT = pari('intnum(x=[1,-1/2],[oo,-3/2], 1/sqrt(x^3-x))')


def primes_of(n):
    return [int(p) for p in pari.factor(n)[0]]


def kron(a, b):
    return int(pari.kronecker(a, b))


def fund_disc_neg(d):
    """fundamental discriminant of Q(sqrt(-d)), d > 0 squarefree."""
    return -d if (-d) % 4 == 1 else -4 * d


def prime_discs(D):
    """factor fundamental discriminant D into prime discriminants."""
    ps = primes_of(abs(D))
    out = []
    rest = D
    for p in ps:
        if p == 2:
            continue
        ps_ = p if p % 4 == 1 else -p
        out.append(ps_)
    prod = 1
    for x in out:
        prod *= x
    if D % 2 == 0:
        out.append(D // prod)   # -4, 8 or -8
    assert eval('*'.join(map(str, out)) if out else '1') == D
    return out


def redei_g(d):
    """g(d) = 1 iff the 4-rank of Cl(Q(sqrt -d)) is 0 (Redei)."""
    if d == 1:
        return 1
    D = fund_disc_neg(d)
    pd = prime_discs(D)
    t = len(pd)
    rows = []
    for i in range(t):
        pi = abs(pd[i]) if pd[i] % 2 else 2
        row = []
        for j in range(t):
            if i == j:
                row.append(0)
            else:
                row.append(1 if kron(pd[j], pi) == -1 else 0)
        row[i] = sum(row) % 2
        rows.append(row)
    M = pari.matrix(t, t, [x for r in rows for x in r]) * pari.Mod(1, 2)
    rk = int(pari.matrank(M))
    r4 = t - 1 - rk
    return 1 if r4 == 0 else 0


def pari_g(d):
    if d == 1:
        return 1
    cyc = pari.quadclassunit(fund_disc_neg(d))[1]
    return 1 if all(int(c) % 4 != 0 for c in cyc) else 0


def g(d):
    a, b = redei_g(d), pari_g(d)
    assert a == b, ('g mismatch', d, a, b)
    return a


def divisors(n):
    ps = primes_of(n)
    out = []
    for r in range(len(ps) + 1):
        for c in itertools.combinations(ps, r):
            x = 1
            for p in c:
                x *= p
            out.append(x)
    return sorted(out)


def set_partitions(items):
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for p in set_partitions(rest):
        yield [[first]] + p
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]


def prod(xs):
    r = 1
    for x in xs:
        r *= x
    return r


def genus_sums(n, gcache):
    """For n = 5 mod 8: (T5a, T5b) mod 2 as set-partition sums."""
    ps = primes_of(n)
    T5a = T5b = 0
    for part in set_partitions(ps):
        blocks = [prod(b) for b in part]
        cls = sorted(b % 8 for b in blocks)
        w = 1
        for b in blocks:
            if b not in gcache:
                gcache[b] = g(b)
            w &= gcache[b]
        if not w:
            continue
        non1 = [c for c in cls if c != 1]
        if non1 == [5]:
            T5a ^= 1
        elif non1 == [3, 7]:
            T5b ^= 1
    return T5a, T5b


def calL2_rank0(d):
    """calL(d)^2 for odd squarefree d with ord_{s=1} = 0 (or the value 0)."""
    k = len(primes_of(d)) if d > 1 else 0
    E = pari.ellinit([0, 0, 0, -d * d, 0])
    L1 = pari.lfun(pari.lfuncreate(E), 1)
    Om = 2 / pari.sqrt(d) * OMEGA_INT
    return L1 / (pari(2) ** (2 * k - 3) * Om)


def nearest_square_root(x, tol=1e-15):
    """return integer r >= 0 with r^2 ~ x (relative tol), else None."""
    xf = float(x)
    if abs(xf) < 1e-12:
        return 0
    r = round(xf ** 0.5)
    for c in (r - 1, r, r + 1):
        if c >= 0 and abs(c * c - xf) <= max(1e-9, tol * abs(xf)):
            return c
    return None
