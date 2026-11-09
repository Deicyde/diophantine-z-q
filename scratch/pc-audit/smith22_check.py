"""Independent check of Smith, arXiv:1603.08479v2, Theorem 2.2 (Table 2) and Table 1.

For squarefree n > 0 we compute
  * g(d) = #2Cl(Q(sqrt(-d))) mod 2 for every positive d | n, from PARI class groups
    (independent of Redei theory): g(d) = 1 iff Cl has no element of order 4;
  * the Tian-Yuan-Zhang genus sums L_x(n) (Smith's second column, equivalently the
    coefficients appearing at the end of the proof of TYZ Theorem 3.? (thm m3) in arXiv v1);
  * Smith's determinants det M_x (third column), from Legendre symbols only;
  * Smith's Table 1 Redei determinant for g(n).
and compare.  Usage: smith22_check.py MAXN NRANDOM SEED
"""
import sys, random
from functools import lru_cache
import cypari2

pari = cypari2.Pari()
pari.allocatemem(2 * 10 ** 9)


def leg(a, p):  # additive Legendre symbol [a/p]_+ in F_2
    a %= p
    return 0 if pow(a, (p - 1) // 2, p) == 1 else 1


def det2(rows, n):
    """determinant over F_2 of n x n matrix given as list of int bitrows"""
    rows = list(rows)
    for c in range(n):
        piv = next((i for i in range(c, n) if rows[i] >> c & 1), None)
        if piv is None:
            return 0
        rows[c], rows[piv] = rows[piv], rows[c]
        for i in range(c + 1, n):
            if rows[i] >> c & 1:
                rows[i] ^= rows[c]
    return 1


def mat_from(M):
    return [sum((M[i][j] & 1) << j for j in range(len(M[i]))) for i in range(len(M))]


_g = {}


def g(d):
    if d == 1:
        return 1
    if d in _g:
        return _g[d]
    D = -d if d % 4 == 3 else -4 * d
    cyc = [int(c) for c in pari.quadclassunit(D)[1]]
    val = 1 if all(c % 4 != 0 for c in cyc) else 0
    _g[d] = val
    return val


def run(n, sums=True):
    ps = [int(p) for p in pari.factor(n)[0]]
    two = 2 in ps
    odd = [p for p in ps if p != 2]
    r = len(odd)
    # divisors as (mask over odd primes, has2)
    def val(mask, t):
        v = 2 if t else 1
        for i in range(r):
            if mask >> i & 1:
                v *= odd[i]
        return v

    @lru_cache(maxsize=None)
    def Lsha(mask):  # Smith's recursive L on odd divisors (L(m)=0 unless m=1 mod 8)
        if mask == 0:
            return 1
        m = val(mask, False)
        if m % 8 != 1:
            return 0
        low = mask & -mask  # fix the prime of lowest index
        s = 0
        sub = mask
        while sub:
            if sub & low:
                d = val(sub, False)
                if d % 8 == 1:
                    s ^= g(d) & Lsha(mask ^ sub)
            sub = (sub - 1) & mask
        return s

    full = (1 << r) - 1
    def subsets(mask):
        sub = mask
        while True:
            yield sub
            if sub == 0:
                break
            sub = (sub - 1) & mask

    t = n % 8
    L = {}
    # sums over d | n; d may contain 2 only if n even.  L(n/d) needs n/d odd = 1 mod 8.
    def S1(cond):
        s = 0
        for sub in subsets(full):
            for t2 in ([True] if two else [False]):
                d = val(sub, t2)
                if d > 1 and cond(d):
                    s ^= g(d) & Lsha(full ^ sub)
        return s

    def S2(c0, c1):
        s = 0
        for sub in subsets(full):
            for sub0 in subsets(sub):
                sub1 = sub ^ sub0
                for (t0, t1) in ([(True, False), (False, True)] if two else [(False, False)]):
                    d0, d1 = val(sub0, t0), val(sub1, t1)
                    if d0 > 1 and d1 > 1 and c0(d0) and c1(d1):
                        s ^= g(d0) & g(d1) & Lsha(full ^ sub)
        return s

    if sums:
        if t == 1:
            L['1'] = Lsha(full)
        elif t == 2 or t == 6 or t == 3 or t in (5, 7):
            pass
        if t == 2:
            L['2'] = S1(lambda d: d % 16 == n % 16)
        if t == 3:
            L['3'] = S1(lambda d: d % 8 == 3)
        if t == 5:
            L['5a'] = S1(lambda d: d % 8 == 5)
            L['5b'] = S2(lambda d: d % 8 == 7, lambda d: d % 8 == 3)
        if t == 6:
            L['6'] = S2(lambda d: d % 16 == (7 * n) % 16, lambda d: d % 8 == 7) ^ S1(lambda d: d % 16 == n % 16)
        if t == 7:
            L['7a'] = S1(lambda d: d % 8 == 7)
            L['7b'] = S2(lambda d: d % 8 == 5, lambda d: d % 8 == 3)

    # Smith's matrices
    A = [[0] * r for _ in range(r)]
    for i in range(r):
        for j in range(r):
            if i != j:
                A[i][j] = leg(odd[j], odd[i])
        A[i][i] = sum(A[i]) % 2
    y = [leg(-1, p) for p in odd]
    z = [leg(2, p) for p in odd]
    At = [[A[j][i] for j in range(r)] for i in range(r)]
    S = [[(A[i][j] + At[i][j]) % 2 for j in range(r)] for i in range(r)]
    Syz = [[(S[i][j] + (y[i] + z[i] if i == j else 0)) % 2 for j in range(r)] for i in range(r)]
    Dz = [[z[i] if i == j else 0 for j in range(r)] for i in range(r)]
    yz = [(a + b) % 2 for a, b in zip(y, z)]
    O = [0] * r

    def block(rows_of_blocks):
        out = []
        for br in rows_of_blocks:
            h = len(br[0]) if isinstance(br[0][0], list) else 1
            for i in range(h):
                row = []
                for B in br:
                    row += B[i] if isinstance(B[0], list) else [B[i]] if False else B[i]
                out.append(row)
        return out

    def col(v):
        return [[x] for x in v]

    def rowv(v):
        return [list(v)]

    def Z(a, b):
        return [[0] * b for _ in range(a)]

    def M(blocks):
        rows = []
        for br in blocks:
            h = len(br[0])
            for i in range(h):
                rr = []
                for B in br:
                    rr += B[i]
                rows.append(rr)
        return rows

    dets = {}
    if t == 1:
        m = M([[S, At], [A, Dz]])
        dets['1'] = det2(mat_from(m), 2 * r)
    if t == 2:
        m = M([[Syz, At], [A, Dz]])
        dets['2'] = det2(mat_from(m), 2 * r)
    if t == 3:
        m = M([[S, At, col(y)], [A, Dz, Z(r, 1)], [rowv(y), Z(1, r), Z(1, 1)]])
        dets['3'] = det2(mat_from(m), 2 * r + 1)
    if t == 5:
        m = M([[S, At, col(yz)], [A, Dz, Z(r, 1)], [rowv(yz), Z(1, r), Z(1, 1)]])
        dets['5a'] = det2(mat_from(m), 2 * r + 1)
        m = M([[S, At, Z(r, 1)], [A, Dz, col(y)], [Z(1, r), rowv(y), Z(1, 1)]])
        dets['5b'] = det2(mat_from(m), 2 * r + 1)
    if t == 6:
        m = M([[Syz, At, col(y)], [A, Dz, col(y)], [rowv(y), rowv(y), Z(1, 1)]])
        dets['6'] = det2(mat_from(m), 2 * r + 1)
    if t == 7:
        m = M([[S, At, col(yz), Z(r, 1)], [A, Dz, Z(r, 1), col(y)],
               [rowv(yz), Z(1, r), Z(1, 1), Z(1, 1)], [Z(1, r), rowv(y), Z(1, 1), Z(1, 1)]])
        dets['7a'] = det2(mat_from(m), 2 * r + 2)
        m = M([[S, At, col(yz), col(y)], [A, Dz, Z(r, 1), Z(r, 1)],
               [rowv(yz), Z(1, r), Z(1, 1), Z(1, 1)], [rowv(y), Z(1, r), Z(1, 1), Z(1, 1)]])
        dets['7b'] = det2(mat_from(m), 2 * r + 2)

    # Smith Table 1 (Redei) for g(n), n odd or n = 2 mod 4 (n mod 4 = 1, 2, 3)
    red = None
    if n % 4 == 1 and r >= 1:
        m = [A[i][:r - 1] + [z[i]] for i in range(r)]
        red = det2(mat_from(m), r)
    elif n % 4 == 2:
        m = [[(A[i][j] + (z[i] if i == j else 0)) % 2 for j in range(r)] for i in range(r)]
        red = det2(mat_from(m), r) if r else 1
    elif n % 4 == 3 and r >= 1:
        m = [A[i][:r - 1] for i in range(r - 1)]
        red = det2(mat_from(m), r - 1) if r > 1 else 1
    return L, dets, red, (g(n) if sums else None), r


if __name__ == "__main__":
    MAXN = int(sys.argv[1]); NR = int(sys.argv[2]); seed = int(sys.argv[3])
    rng = random.Random(seed)
    ns = [n for n in range(2, MAXN) if pari.issquarefree(n)]
    PB = int(sys.argv[4]) if len(sys.argv) > 4 else 17
    KMAX = int(sys.argv[5]) if len(sys.argv) > 5 else 9
    smallp = [int(p) for p in pari.primes(PB)][1:]
    for _ in range(NR):
        k = rng.randint(4, KMAX)
        ps = rng.sample(smallp, k)
        n = 1
        for p in ps:
            n *= p
        if rng.random() < 0.4:
            n *= 2
        ns.append(n)
    stats = {}
    bad = 0
    redbad = 0
    for n in ns:
        L, D, red, gn, r = run(n)
        for k in L:
            st = stats.setdefault(k, [0, 0, 0])
            st[0] += 1
            st[1] += L[k]
            if L[k] != D[k]:
                st[2] += 1
                bad += 1
                if bad < 20:
                    print("MISMATCH", n, k, "TYZ sum", L[k], "Smith det", D[k])
        if red is not None and red != gn:
            redbad += 1
            if redbad < 10:
                print("REDEI MISMATCH", n, red, gn)
    print("n tested:", len(ns))
    for k in sorted(stats):
        print("row", k, "count", stats[k][0], "nonzero", stats[k][1], "mismatches", stats[k][2])
    print("total mismatches", bad, "Redei table mismatches", redbad)
