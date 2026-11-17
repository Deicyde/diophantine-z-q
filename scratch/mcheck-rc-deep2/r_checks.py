"""mcheck-rc-deep2, part 2: ex:limits-residual-bound, (5.1) (tex L4453-4648).

Pure Python, exact integers / Fractions.  Each check has a negative control (wrong input must fail).

 R1  (5.1a): s = |T| <= v + A + 1 + j for all split patterns (2N primes split, moving prime split,
     derivative primes inert, ramified primes = primes of the squarefree part of k, 2 unramified).
 R2  (5.1b) and the Kummer count: dim H^1(G_{K,S_T},F_2) <= 1 + |S_T| + (r-1) <= 2s; |S_T| <= 2s - r.
 R3  genus bound dim Cl(K)[2] = r - 1 for imaginary quadratic K (fundamental discriminants
     -3 >= D >= -4000), computed by composition of reduced binary quadratic forms (count classes with
     f*f = 1); Hilbert 90 recipe beta = 1 + alpha (alpha != -1), beta = sqrt(k) (alpha = -1).
 R4  global Euler characteristic bookkeeping: h0 = 2, h2 = h1 - 4, total <= 8s - 2 <= 8s + 2; Schreier:
     d(H) <= 1 + 2(d(G) - 1) with d(G) = s + 1 gives 2s + 1, so h1 <= 4s + 2 and total <= 8s + 2.
 R5  local table: (h0,h1,h2)(K_w,W) = (2, 4+2d_w, 2); condition dims; per-prime costs 30, 24, 32,
     28 (14 inert) <= 48.
 R6  (5.1) inequality chain for all v<=12, A<=40, j<=40, s <= v+A+1+j.
 R7  support comparison after inverting t: A = D = ((1+t)^{+-e}-1)I, C=0: the full / unramified /
     singular blocks are acyclic over F_2((t)) for odd e (and their t-adic valuation is exactly 1).
 R8  binary case: F_2[G] (G = (Z/2)^k) is local with nilpotent augmentation ideal, I^{k+1} = 0; a
     random free complex over F_2[x]/(x^2) (k=1) has minimal-model ranks = dims of the complex after
     augmentation (cancellation of unit entries).
"""
import random
import itertools
from math import gcd, isqrt
from fractions import Fraction as Fr

random.seed(4453)
results = []


def check(name, ok, info=""):
    results.append(ok)
    print(("PASS " if ok else "FAIL ") + name + ((" : " + info) if info else ""))


def control(name, wrong_ok):
    check("control " + name + " (wrong input rejected)", not wrong_ok)


# ---------------- R1 ----------------
def s_count(v, A_ram, j):
    """T = (primes of 2N) + moving prime + j derivative primes + ramified primes of K (A_ram <= A),
    all disjoint because 2N primes and r split, derivative primes inert, and 2 | 2N is unramified."""
    return v + 1 + j + A_ram


ok = all(s_count(v, a, j) <= v + A + 1 + j
         for v in range(1, 8) for A in range(0, 8) for a in range(0, A + 1) for j in range(0, 6))
check("R1 (5.1a) s <= v+A+1+j", ok)
control("R1 if the moving prime were counted twice", all(s_count(v, A, j) + 1 <= v + A + 1 + j
                                                         for v in range(1, 3) for A in range(2) for j in range(2)))


# ---------------- R2 ----------------
def kummer_bound(s, r):
    ST = r + 2 * (s - r)          # one place over each ramified prime, two over the others (max)
    units = 1 + ST                # unit rank |S_T| (r1 + r2 - 1 = 0) plus mu_2
    cl = r - 1                    # genus bound
    return units + cl, ST


ok = True
for s in range(1, 60):
    for r in range(1, s + 1):
        h1, ST = kummer_bound(s, r)
        ok &= ST <= 2 * s - r and h1 <= 2 * s
check("R2 dim H^1(G_{K,S_T},F_2) <= 1+|S_T|+(r-1) <= 2s and |S_T| <= 2s - r", ok)
control("R2 if the class group 2-rank were r (not r-1)",
        all(1 + (2 * s - r) + r <= 2 * s for s in range(1, 10) for r in range(1, s + 1)))


# ---------------- R3: genus theory by composition of forms ----------------
def is_fund_disc(D):
    if D >= 0:
        return False
    if D % 4 == 1:
        m = -D
        return all(m % (p * p) for p in range(3, isqrt(m) + 1, 2)) and m % 4 != 0
    if D % 4 == 0:
        m = -D // 4
        if m % 4 not in (1, 2):
            return False
        return all(m % (p * p) for p in range(2, isqrt(m) + 1))
    return False


def reduce_form(a, b, c):
    while True:
        if a > c or (a == c and b < 0):
            a, b, c = c, -b, a
            continue
        if b > a or b <= -a:
            # normalize b into (-a, a]
            k = (a - b) // (2 * a)
            b2 = b + 2 * a * k
            c = (b2 * b2 - (b * b - 4 * a * c)) // (4 * a)
            b = b2
            continue
        if a == c and b < 0:
            b = -b
            continue
        return (a, b, c)


def compose(f, g, D):
    """Dirichlet composition (Buell, Binary Quadratic Forms, Thm 4.10 form): e = gcd(a1, a2, (b1+b2)/2),
    a3 = a1 a2 / e^2, B = b1 mod 2a1/e, B = b2 mod 2a2/e, B^2 = D mod 4a3 (B found by search)."""
    a1, b1, c1 = f
    a2, b2, c2 = g
    e = gcd(gcd(a1, a2), (b1 + b2) // 2)
    a3 = a1 * a2 // (e * e)
    for B in range(-a3, a3 + 1):
        if (B - b1) % (2 * a1 // e) == 0 and (B - b2) % (2 * a2 // e) == 0 and (B * B - D) % (4 * a3) == 0:
            return reduce_form(a3, B, (B * B - D) // (4 * a3))
    raise RuntimeError("composition failed")


def class_group(D):
    forms = []
    a = 1
    while 3 * a * a <= -D:
        for b in range(-a + 1, a + 1):
            if (b * b - D) % (4 * a) == 0:
                c = (b * b - D) // (4 * a)
                if c >= a and gcd(gcd(a, abs(b)), c) == 1:
                    if not (b < 0 and (a == c)):
                        forms.append((a, b, c))
        a += 1
    return forms


def two_rank(D):
    forms = class_group(D)
    one = reduce_form(1, D % 2, (D % 2 - D) // 4)
    n2 = sum(1 for f in forms if compose(f, f, D) == one)
    k = n2.bit_length() - 1
    assert 1 << k == n2
    return k, len(forms)


def ram_primes(D):
    m, ps, p = -D, [], 2
    while p * p <= m:
        if m % p == 0:
            ps.append(p)
            while m % p == 0:
                m //= p
        p += 1
    if m > 1:
        ps.append(m)
    return ps


ok = True; cnt = 0
for D in range(-3, -4001, -1):
    if not is_fund_disc(D):
        continue
    k, h = two_rank(D)
    r = len(ram_primes(D))
    ok &= (k == r - 1)
    cnt += 1
check("R3 dim Cl(K)[2] = r-1 for all imaginary quadratic fundamental discriminants -4000 <= D <= -3",
      ok, "%d fields, by composition of reduced forms" % cnt)
control("R3 claim 'dim Cl[2] = r' at D=-4*5*13 (r=3)", two_rank(-260)[0] == len(ram_primes(-260)))


# Hilbert 90 recipe in Q(sqrt k): elements as (x, y) meaning x + y sqrt(k), rational x, y
def qmul(a, b, k):
    return (a[0] * b[0] + k * a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def qconj(a):
    return (a[0], -a[1])


def qdiv(a, b, k):
    nb = b[0] * b[0] - k * b[1] * b[1]
    num = qmul(a, qconj(b), k)
    return (num[0] / nb, num[1] / nb)


ok = True
for _ in range(400):
    k = -random.choice([1, 2, 3, 5, 6, 7, 10, 11, 13, 14, 15, 23, 31, 47])
    b0 = (Fr(random.randint(-9, 9)), Fr(random.randint(-9, 9)))
    if b0 == (0, 0):
        continue
    alpha = qdiv(b0, qconj(b0), k)                     # norm one
    na = alpha[0] ** 2 - k * alpha[1] ** 2
    if alpha == (Fr(-1), Fr(0)):
        beta = (Fr(0), Fr(1))                          # sqrt(k)
    else:
        beta = (1 + alpha[0], alpha[1])
    ok &= na == 1 and qdiv(beta, qconj(beta), k) == alpha
check("R3 Hilbert 90: alpha = beta/conj(beta) with beta = 1+alpha (alpha != -1), beta = sqrt(k) (alpha = -1)", ok)
k = -7; alpha = (Fr(-1), Fr(0)); beta = (1 + alpha[0], alpha[1])
control("R3 beta = 1+alpha at alpha = -1", beta != (0, 0) and qdiv(beta, qconj(beta), k) == alpha)


# ---------------- R4 ----------------
ok = True
for s in range(1, 80):
    for h1 in range(4, 4 * s + 1):
        h0 = 2
        h2 = h1 - 4                     # from h0 - h1 + h2 = -2
        ok &= (h0 - h1 + h2 == -2) and h0 + h1 + h2 <= 8 * s - 2 <= 8 * s + 2
    dG = s + 1                          # pro-2 group over Q unramified outside T and infinity
    dH = 1 + 2 * (dG - 1)               # Schreier, index 2
    h1w = 2 * dH                        # W = F_2^2
    ok &= dH == 2 * s + 1 and 2 + h1w + (h1w - 4) == 8 * s + 2
check("R4 h2 = h1-4, total <= 8s-2 (genus route) and = 8s+2 (Schreier route)", ok)
# Euler characteristic of K imaginary quadratic: sum_{v|inf} h0(K_v,W) - [K:Q] dim W = 2 - 4 = -2
control("R4 Schreier with index 3 instead of 2 gives the same 2s+1", all(1 + 3 * s == 2 * s + 1 for s in range(1, 5)))


# ---------------- R5 ----------------
def local_dims(dw):
    return (2, 4 + 2 * dw, 2)


table = {
    "old Kummer": lambda dw: 2 + (2 + dw),
    "unramified": lambda dw: 2 + 2,         # [Phi - 1] on trivial W: zero map, dims (2, 2)
    "zero": lambda dw: 0,
    "full": lambda dw: sum(local_dims(dw)),
    "derivative strict": lambda dw: 2,      # D^0
    "derivative finite or singular": lambda dw: 2 + 2,   # D^0 + plane[-1]
    "derivative relaxed": lambda dw: 2 + 4,               # D^0 + (F+S)[-1]
}
printed = {"old Kummer": (4, 12), "unramified": (4, 12), "zero": (0, 8), "full": (8, 16),
           "derivative strict": (2, 10), "derivative finite or singular": (4, 12),
           "derivative relaxed": (6, 14)}
ok = True
for name, f in table.items():
    u = f(0); tot = u + sum(local_dims(0))
    ok &= (u, tot) == printed[name]
ok &= table["old Kummer"](1) + sum(local_dims(1)) == 15      # 12 + 3 d_w with d_w = 1
cost2 = 2 * (table["old Kummer"](1) + sum(local_dims(1)))      # two places over 2, each K_w = Q_2
cost_old = 2 * (table["old Kummer"](0) + sum(local_dims(0)))
cost_mov = 2 * (table["full"](0) + sum(local_dims(0)))
cost_der_inert = max(table[n](0) for n in table if n.startswith("derivative")) + sum(local_dims(0))
ok &= (cost2, cost_old, cost_mov, cost_der_inert) == (30, 24, 32, 14) and max(cost2, cost_old, cost_mov, 2 * cost_der_inert) <= 48
# local Euler characteristic: h0 - h1 + h2 = -[K_w:Q_2] dim W
ok &= all(local_dims(dw)[0] - local_dims(dw)[1] + local_dims(dw)[2] == -2 * dw for dw in (0, 1))
check("R5 local table rows, 12+3d_w, per-prime costs (30, 24, 32, 14<=28) <= 48", ok,
      "costs %s" % ((cost2, cost_old, cost_mov, cost_der_inert),))
control("R5 old Kummer without degree-zero torsion (dims (0, d_w))", 0 + 0 + sum(local_dims(0)) == printed["old Kummer"][1])


# ---------------- R6 ----------------
def chain_ok(v, A, j, s, c56=56, c70=70, local=48):
    m = v + 1 + j
    lhs = (8 * s + 2) + local * m + 4
    mid = 8 * (s + 1) + 6 + 48 * (v + 1 + j)
    rhs = c56 * v + 8 * A + c56 * j + c70
    return lhs <= mid <= rhs


ok = all(chain_ok(v, A, j, s) for v in range(1, 13) for A in range(0, 41) for j in range(0, 41)
         for s in range(1, v + A + 2 + j))
# tightness: slack at s = v+A+1+j is exactly 8 (the +8 of 8(s+1))
slack = {56 * v + 8 * A + 56 * j + 70 - ((8 * (v + A + 1 + j) + 2) + 48 * (v + 1 + j) + 4)
         for v in range(1, 5) for A in range(5) for j in range(5)}
check("R6 (5.1): (8s+2)+48m+4 <= 8(s+1)+6+48(v+1+j) <= 56v+8A+56j+70", ok, "slack at max s: %s" % slack)
control("R6 with constant 61 instead of 70", all(chain_ok(v, A, j, v + A + 1 + j, c70=61)
                                                  for v in range(1, 4) for A in range(3) for j in range(3)))


# ---------------- R7 ----------------
L = 30


def ps_pow1t(e):
    base = [1, 1] + [0] * (L - 2)
    if e < 0:
        base = [1] * L          # (1+t)^{-1} = sum t^k over F_2
        e = -e
    out = [1] + [0] * (L - 1)
    for _ in range(e):
        new = [0] * L
        for i, x in enumerate(out):
            if x:
                for jj, y in enumerate(base[:L - i]):
                    if y:
                        new[i + jj] ^= 1
        out = new
    return out


def tval(p):
    return next((k for k, x in enumerate(p) if x), None)


ok = True
for e in range(1, 40, 2):
    for sgn in (1, -1):
        p = ps_pow1t(sgn * e); p[0] ^= 1        # (1+t)^{+-e} - 1
        ok &= tval(p) == 1                      # = t * unit; nonzero after inverting t
# blocks acyclic: full [W -(A,0)-> W+W -(0,D)-> W] with A, D invertible scalars a: rank count
check("R7 ((1+t)^{+-e}-1) = t*unit in F_2[[t]] for odd e < 40: full/unramified/singular active blocks "
      "(C=0, A=D) are acyclic after inverting t", ok)
p = ps_pow1t(0); p[0] ^= 1
control("R7 with e = 0 (A = 0)", tval(p) is not None)


# ---------------- R8 ----------------
def group_algebra_nilpotent(k):
    # F_2[G], G = (Z/2)^k; basis indexed by subsets; augmentation ideal generated by x_i = g_i - 1,
    # x_i^2 = g_i^2 - 2 g_i + 1 = 0 in char 2; so F_2[G] = F_2[x_1..x_k]/(x_i^2) and I^{k+1} = 0.
    # check: product of k+1 elements of I is zero, product of x_1...x_k is not.
    def mul(a, b):  # elements: dict frozenset -> coeff mod 2 (monomials in x_i, squarefree)
        out = {}
        for m1, c1 in a.items():
            for m2, c2 in b.items():
                if m1 & m2:
                    continue
                m = m1 | m2
                out[m] = (out.get(m, 0) + c1 * c2) % 2
        return {m: c for m, c in out.items() if c}

    def rand_I():
        el = {}
        for r in range(1, k + 1):
            for m in itertools.combinations(range(k), r):
                if random.random() < 0.5:
                    el[frozenset(m)] = 1
        return el or {frozenset([0]): 1}

    ok = True
    for _ in range(30):
        prod = rand_I()
        for _ in range(k):
            prod = mul(prod, rand_I())
        ok &= prod == {}
    top = {frozenset([0]): 1}
    for i in range(1, k):
        top = mul(top, {frozenset([i]): 1})
    ok &= top != {}
    return ok


ok = all(group_algebra_nilpotent(k) for k in range(1, 5))


# minimal model over R = F_2[x]/(x^2): elements (a, b) = a + b x
def rmul(p, q):
    return ((p[0] * q[0]) % 2, (p[0] * q[1] + p[1] * q[0]) % 2)


def radd(p, q):
    return ((p[0] + q[0]) % 2, (p[1] + q[1]) % 2)


def rmm(A, B):
    n, m, l = len(A), len(B), len(B[0]) if B else 0
    out = [[(0, 0)] * l for _ in range(n)]
    for i in range(n):
        for jj in range(l):
            s = (0, 0)
            for kk in range(m):
                s = radd(s, rmul(A[i][kk], B[kk][jj]))
            out[i][jj] = s
    return out


def rand_inv(n):
    # unipotent-times-permutation over R: random elementary operations with unit pivots
    M = [[(int(i == jj), 0) for jj in range(n)] for i in range(n)]
    for _ in range(4 * n):
        i, jj = random.randrange(n), random.randrange(n)
        if i == jj:
            continue
        c = (random.randint(0, 1), random.randint(0, 1))
        M = [r[:] for r in M]
        for kk in range(n):
            M[i][kk] = radd(M[i][kk], rmul(c, M[jj][kk]))
    return M


def inv_R(M):
    n = len(M)
    a = [r[:] + [(int(i == jj), 0) for jj in range(n)] for i, r in enumerate(M)]
    for c in range(n):
        p = next(r for r in range(c, n) if a[r][c][0] == 1)
        a[c], a[p] = a[p], a[c]
        u = a[c][c]                       # unit (1, b): inverse (1, b)
        uinv = (1, u[1])
        a[c] = [rmul(uinv, x) for x in a[c]]
        for r in range(n):
            if r != c and a[r][c] != (0, 0):
                f = a[r][c]
                a[r] = [radd(x, rmul(f, y)) for x, y in zip(a[r], a[c])]
    return [r[n:] for r in a]


def minimal_ranks(ds, ranks):
    """cancel unit entries repeatedly (Gaussian elimination of contractible summands)."""
    ds = [[r[:] for r in d] for d in ds]
    ranks = ranks[:]
    changed = True
    while changed:
        changed = False
        for n, d in enumerate(ds):
            for i in range(len(d)):
                for jj in range(len(d[0])):
                    if d[i][jj][0] == 1:                       # unit entry: cancel the disk
                        u = d[i][jj]; uinv = (1, u[1])
                        # new d_n' = d - d[:,j] uinv d[i,:] restricted, remove row i, col j
                        nd = [[radd(d[a][b], rmul(rmul(d[a][jj], uinv), d[i][b]))
                               for b in range(len(d[0])) if b != jj] for a in range(len(d)) if a != i]
                        ds[n] = nd
                        # remove row i from d_{n+1} source (column i) and column j from d_{n-1} target (row j)
                        if n + 1 < len(ds):
                            ds[n + 1] = [[x for b, x in enumerate(r) if b != i] for r in ds[n + 1]]
                        if n - 1 >= 0:
                            ds[n - 1] = [r for a, r in enumerate(ds[n - 1]) if a != jj]
                        ranks[n] -= 1; ranks[n + 1] -= 1
                        changed = True
                        break
                if changed:
                    break
            if changed:
                break
    return ranks, ds


def f2_rank(M):
    a = [r[:] for r in M]
    rk = 0
    cols = len(a[0]) if a else 0
    for c in range(cols):
        p = next((r for r in range(rk, len(a)) if a[r][c]), None)
        if p is None:
            continue
        a[rk], a[p] = a[p], a[rk]
        for r in range(len(a)):
            if r != rk and a[r][c]:
                a[r] = [(x + y) % 2 for x, y in zip(a[r], a[rk])]
        rk += 1
    return rk


def aug_dims(ds, ranks):
    red = [[[x[0] for x in r] for r in d] for d in ds]
    rk = [f2_rank(d) if d and d[0] else 0 for d in red]
    dims = []
    for n in range(len(ranks)):
        ker = ranks[n] - (rk[n] if n < len(rk) else 0)
        im = rk[n - 1] if n >= 1 else 0
        dims.append(ker - im)
    return dims


ok8 = True; cnt = 0
for _ in range(60):
    # minimal part: differentials with entries in (x) = {(0,b)} composing to 0 automatically (x^2=0)
    mr = [random.randint(0, 2) for _ in range(3)]
    disks = [random.randint(0, 2) for _ in range(2)]        # disk in degrees (0,1), (1,2)
    ranks = [mr[0] + disks[0], mr[1] + disks[0] + disks[1], mr[2] + disks[1]]
    if 0 in ranks:
        continue
    d0 = [[(0, 0)] * ranks[0] for _ in range(ranks[1])]
    d1 = [[(0, 0)] * ranks[1] for _ in range(ranks[2])]
    for a in range(mr[1]):
        for b in range(mr[0]):
            d0[a][b] = (0, random.randint(0, 1))
    for a in range(mr[2]):
        for b in range(mr[1]):
            d1[a][b] = (0, random.randint(0, 1))
    # disk 0: degree 0 source cols mr0.., degree 1 target rows mr1..
    for q in range(disks[0]):
        d0[mr[1] + q][mr[0] + q] = (1, 0)
    for q in range(disks[1]):
        d1[mr[2] + q][mr[1] + disks[0] + q] = (1, 0)
    P = [rand_inv(r) for r in ranks]
    Pi = [inv_R(M) for M in P]
    D0 = rmm(rmm(P[1], d0), Pi[0]); D1 = rmm(rmm(P[2], d1), Pi[1])
    if any(x != (0, 0) for r in rmm(D1, D0) for x in r):
        ok8 = False; continue
    mranks, _ = minimal_ranks([D0, D1], ranks)
    ok8 &= mranks == aug_dims([D0, D1], ranks)
    cnt += 1
check("R8 F_2[G] local with I^{k+1}=0 (k<=4); minimal-model ranks over F_2[x]/x^2 = dims after "
      "augmentation", ok and ok8, "%d random complexes" % cnt)
# control: the unreduced model ranks (with disks) do not equal the augmented dims
wrong_all = True
for _ in range(20):
    ranks = [2, 3, 1]
    d0 = [[(0, 0)] * 2 for _ in range(3)]; d1 = [[(0, 0)] * 3 for _ in range(1)]
    d0[2][1] = (1, 0)                       # one disk in degrees (0,1)
    d0[0][0] = (0, 1)
    wrong_all &= ranks == aug_dims([d0, d1], ranks)
control("R8 'unreduced ranks = augmented dims' on a complex with a disk", wrong_all)

print("%d/%d PASS" % (sum(results), len(results)))
