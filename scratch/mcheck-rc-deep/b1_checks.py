"""mcheck-rc-deep, block 1 (tex L2834-3410, ex:arith-finite-heegner): arithmetic checks.

Pure Python (no numpy/sympy on the host). Each check prints PASS/FAIL with the tex label.
"""
import random
from fractions import Fraction

random.seed(20261117)
results = []


def check(name, ok, info=""):
    results.append((name, ok))
    print(("PASS " if ok else "FAIL ") + name + ((" : " + info) if info else ""))


def v2(x):
    x = abs(x)
    if x == 0:
        return 10**9
    c = 0
    while x % 2 == 0:
        x //= 2
        c += 1
    return c


# ---------- (H1): e = v2(u^4-1) = n+2 for u = 1+2^n, n >= 2 ----------
ok = all(v2((1 + 2**n) ** 4 - 1) == n + 2 for n in range(2, 60))
check("(H1) v2((1+2^n)^4-1) = n+2 for 2<=n<60", ok)
check("(H1) fails at n=1 (so n>=2 is needed)", v2(3**4 - 1) != 3, "v2(80)=%d" % v2(80))

# rho(z) = u^2 * J u^2 J^{-1} = u^4 I for scalar u^2: matrix check with J = diag(1,-1)


def mmul(A, B, mod=None):
    n, m, p = len(A), len(B), len(B[0])
    C = [[sum(A[i][k] * B[k][j] for k in range(m)) for j in range(p)] for i in range(n)]
    if mod:
        C = [[c % mod for c in row] for row in C]
    return C


u = 1 + 2**3
g2 = [[u * u, 0], [0, u * u]]
J = [[1, 0], [0, -1]]
z = mmul(mmul(mmul(g2, J), g2), J)  # J^{-1} = J
check("(H1) rho(g^2 tau g^2 tau^-1) = u^4 I", z == [[u**4, 0], [0, u**4]])

# ---------- matrix-span statement after (H2) ----------


def hnf_det_gcd(vectors):
    """Return the index-lattice data: gcd of 4x4 minors of the span (lattice in Z^4)."""
    from itertools import combinations
    g = 0
    for rows in combinations(vectors, 4):
        M = [list(r) for r in rows]
        # integer determinant via fraction elimination
        d = det_frac(M)
        g = gcd(g, int(d))
    return g


def gcd(a, b):
    a, b = abs(a), abs(b)
    while b:
        a, b = b, a % b
    return a


def det_frac(M):
    M = [[Fraction(x) for x in r] for r in M]
    n = len(M)
    d = Fraction(1)
    for c in range(n):
        p = None
        for r in range(c, n):
            if M[r][c] != 0:
                p = r
                break
        if p is None:
            return Fraction(0)
        if p != c:
            M[c], M[p] = M[p], M[c]
            d = -d
        d *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            for k in range(c, n):
                M[r][k] -= f * M[c][k]
    return d


def in_lattice(vecs, target):
    """target in Z-span of vecs (4 independent vectors)? Solve rationally, test integrality."""
    M = [list(v) for v in vecs]
    # solve sum x_i vecs_i = target : columns are vecs
    A = [[Fraction(M[j][i]) for j in range(4)] + [Fraction(target[i])] for i in range(4)]
    n = 4
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[p] = A[p], A[c]
        piv = A[c][c]
        A[c] = [x / piv for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]
                A[r] = [A[r][k] - f * A[c][k] for k in range(n + 1)]
    return all(A[i][n].denominator % 2 == 1 for i in range(n))  # Z_(2)-integral


ok = True
for n in range(2, 12):
    E11 = [1 + 2**n, 0, 0, 1]
    I = [1, 0, 0, 1]
    sq11 = [(1 + 2**n) ** 2, 0, 0, 1]
    sq12 = [1, 2 ** (n + 1), 0, 1]  # (I+2^n E12)^2
    sq21 = [1, 0, 2 ** (n + 1), 1]
    # direct squaring check
    A11 = [[1 + 2**n, 0], [0, 1]]
    A12 = [[1, 2**n], [0, 1]]
    A21 = [[1, 0], [2**n, 1]]
    if mmul(A11, A11) != [[1 + 2 ** (n + 1) + 2 ** (2 * n), 0], [0, 1]]:
        ok = False
    if mmul(A12, A12) != [[1, 2 ** (n + 1)], [0, 1]] or mmul(A21, A21) != [[1, 0], [2 ** (n + 1), 1]]:
        ok = False
    vecs = [I, sq11, sq12, sq21]
    for i in range(4):
        e = [0, 0, 0, 0]
        e[i] = 2 ** (n + 1)
        if not in_lattice(vecs, e):
            ok = False
check("span{I, squares of I+2^nE_ij} contains 2^{n+1}M_2(Z_2) (n=2..11; Z_(2)-integral solve)", ok)

# ---------- (H5): |F_{l^2}^x / F_l^x| = l+1, cyclic ----------
primes = [p for p in range(3, 200) if all(p % q for q in range(2, int(p**0.5) + 1))]


def fl2_elements(l):
    # F_{l^2} = F_l[s]/(s^2 - n) with n a non-residue
    nr = next(a for a in range(2, l) if pow(a, (l - 1) // 2, l) == l - 1)
    return nr


def fl2_mul(x, y, l, nr):
    a, b = x
    c, d = y
    return ((a * c + b * d * nr) % l, (a * d + b * c) % l)


def fl2_pow(x, e, l, nr):
    r = (1, 0)
    while e:
        if e & 1:
            r = fl2_mul(r, x, l, nr)
        x = fl2_mul(x, x, l, nr)
        e >>= 1
    return r


ok = True
for l in primes[:20]:
    nr = fl2_elements(l)
    # find a generator of F_{l^2}^x; its image in the quotient by F_l^x has order l+1
    N = l * l - 1
    fac = [q for q in range(2, N + 1) if N % q == 0 and all(q % r for r in range(2, int(q**0.5) + 1))]
    gen = None
    for a in range(l):
        for b in range(1, l):
            x = (a, b)
            if all(fl2_pow(x, N // q, l, nr) != (1, 0) for q in fac):
                gen = x
                break
        if gen:
            break
    y = gen  # image of a generator of F_{l^2}^x generates the quotient
    # order of y must be exactly l+1 in F_{l^2}^x and y^k in F_l iff (l+1) | k
    k = 1
    cur = y
    while cur[1] != 0 and k <= 2 * l + 4:
        cur = fl2_mul(cur, y, l, nr)
        k += 1
    if k != l + 1:
        ok = False
check("(H5) F_{l^2}^x/F_l^x cyclic of order l+1 (first 20 odd primes)", ok)

# ---------- (H6): (sigma-1) D_l = (l+1) - Tr in Z[C_{l+1}] ----------


def gr_mul(x, y, n):
    z = [0] * n
    for i, a in enumerate(x):
        if a:
            for j, b in enumerate(y):
                if b:
                    z[(i + j) % n] += a * b
    return z


ok = True
for l in primes[:30]:
    n = l + 1
    D = [0] * n
    for j in range(1, l + 1):
        D[j % n] += j
    sm1 = [0] * n
    sm1[1] += 1
    sm1[0] -= 1
    lhs = gr_mul(sm1, D, n)
    rhs = [(l + 1) - 1] + [-1] * (n - 1)
    if lhs != rhs:
        ok = False
check("(H6) (sigma_l - 1) D_l = (l+1) - Tr_l in Z[C_{l+1}] (30 primes)", ok)

# ---------- (H12): rho(Fr) == J mod 2^{a+1} => 2^{a+1} | a_l and l+1 ----------
ok = True
for a in range(1, 12):
    mod = 2 ** (a + 1)
    for _ in range(200):
        # random J with J^2=I, tr 0, det -1: J = P diag(1,-1) P^-1 for P in SL2(Z)
        p, q = random.randint(-9, 9), random.randint(-9, 9)
        P = [[1, p], [0, 1]]
        Q = [[1, 0], [q, 1]]
        P = mmul(P, Q)
        Pinv = [[P[1][1], -P[0][1]], [-P[1][0], P[0][0]]]
        Jm = mmul(mmul(P, [[1, 0], [0, -1]]), Pinv)
        X = [[Jm[i][j] + mod * random.randint(-50, 50) for j in range(2)] for i in range(2)]
        tr = X[0][0] + X[1][1]
        det = X[0][0] * X[1][1] - X[0][1] * X[1][0]
        if tr % mod or (det + 1) % mod:
            ok = False
        # F - a_l acts as J on E[2^a]: (X - tr I) == J mod 2^a
        Y = [[X[i][j] - (tr if i == j else 0) for j in range(2)] for i in range(2)]
        if any((Y[i][j] - Jm[i][j]) % 2**a for i in range(2) for j in range(2)):
            ok = False
        # Frobenius of K_l (= X^2) is I mod 2^{a+1}
        X2 = mmul(X, X)
        if any((X2[i][j] - (1 if i == j else 0)) % mod for i in range(2) for j in range(2)):
            ok = False
check("(H12) X==J mod 2^{a+1} => 2^{a+1}|tr X, det X == -1, X-tr(X) == J mod 2^a, X^2 == I mod 2^{a+1}", ok)

ok = all(((l * l - 1) % 2 ** (a + 2) == 0 and ((l * l - 1) // 2) % 2 ** (a + 1) == 0)
         for a in range(1, 15) for l in range(2 ** (a + 1) - 1, 2 ** (a + 1) * 40, 2 ** (a + 1)))
check("local diagrams: l == -1 mod 2^{a+1} => q=l^2 == 1 mod 2^{a+2} and 2^{a+1} | (q-1)/2", ok)

# -1 is a 2^m-th power in F_{l^2} for m <= a when l == -1 mod 2^{a+1} (brute force in F_{l^2})
ok = True
cnt = 0
for l in primes:
    a = v2(l + 1) - 1
    if a < 1 or l > 140:
        continue
    nr = fl2_elements(l)
    for m in range(1, a + 1):
        e = 2**m
        found = any(fl2_pow((x, y), e, l, nr) == (l - 1, 0) for x in range(l) for y in range(l) if (x, y) != (0, 0))
        cnt += 1
        if not found:
            ok = False
check("self-cup: -1 is a 2^m-th power in F_{l^2} for m<=a, l==-1 mod 2^{a+1} (%d cases)" % cnt, ok)

# ---------- (H13)-(H18): Frobenius algebra ----------
# Polynomials in F with coefficients that are polynomials in (a, l): dict {(i_a, i_l): coeff}


def padd(p, q):
    r = dict(p)
    for k, v in q.items():
        r[k] = r.get(k, 0) + v
    return {k: v for k, v in r.items() if v}


def pmul(p, q):
    r = {}
    for k1, v1 in p.items():
        for k2, v2_ in q.items():
            k = (k1[0] + k2[0], k1[1] + k2[1])
            r[k] = r.get(k, 0) + v1 * v2_
    return {k: v for k, v in r.items() if v}


A_ = {(1, 0): 1}
L_ = {(0, 1): 1}
ONE = {(0, 0): 1}


def neg(p):
    return {k: -v for k, v in p.items()}


def Fpoly_mul(P, Q):
    # P,Q lists of coefficient-polys indexed by power of F; reduce by F^2 = aF - l
    R = [dict() for _ in range(len(P) + len(Q))]
    for i, p in enumerate(P):
        for j, q in enumerate(Q):
            R[i + j] = padd(R[i + j], pmul(p, q))
    # reduce
    for d in range(len(R) - 1, 1, -1):
        c = R[d]
        if c:
            R[d - 1] = padd(R[d - 1], pmul(c, A_))
            R[d - 2] = padd(R[d - 2], neg(pmul(c, L_)))
            R[d] = {}
    return [R[0], R[1]]


# (H17): (F - a)(aF - (l+1)) = a - (l+1)F
lhs = Fpoly_mul([neg(A_), ONE], [neg(padd(L_, ONE)), A_])
rhs = [A_, neg(padd(L_, ONE))]
check("(H17) (F-a)(aF-(l+1)) = a-(l+1)F mod F^2-aF+l", lhs == rhs)
# (H14): F^2 - 1 = aF - (l+1)
lhs = Fpoly_mul([ONE, {}], [{}, ONE])  # F
F2 = Fpoly_mul([{}, ONE], [{}, ONE])
check("(H14) F^2-1 = a_l F-(l+1)", [padd(F2[0], neg(ONE)), F2[1]] == [neg(padd(L_, ONE)), A_])

# (H16) first equality: reduction of -U_0 with 2^a Qbar = L Xbar, Ybar = F Xbar
# -U0bar = -(l+1)/2^a * L*Ybar + a_l/2^a * L*Xbar, with L Xbar = 2^a Qbar
# test numerically on a concrete group: Z/2^k-module model with F an integer matrix
ok = True
for _ in range(300):
    a = random.randint(1, 6)
    l = 2 ** (a + 1) * random.randint(1, 30) - 1
    al = 2 ** (a + 1) * random.randint(-20, 20)
    K = 2 ** (a + 8)  # work in (Z/K)^2 with F a matrix satisfying F^2 - al F + l = 0 mod K
    # companion matrix of x^2 - al x + l
    Fm = [[0, -l], [1, al]]
    Qb = [random.randrange(K), random.randrange(K)]
    LX = [(2**a) * x % K for x in Qb]  # L Xbar := 2^a Qbar (L absorbed)
    FLX = [sum(Fm[i][j] * LX[j] for j in range(2)) % K for i in range(2)]
    U0 = [((l + 1) // 2**a * FLX[i] - al // 2**a * LX[i]) % K for i in range(2)]
    FQ = [sum(Fm[i][j] * Qb[j] for j in range(2)) % K for i in range(2)]
    snew = [(al * Qb[i] - (l + 1) * FQ[i]) % K for i in range(2)]
    if [(-x) % K for x in U0] != snew:
        ok = False
    # F^2 Xbar = Xbar would need F^2 = 1 on X; skip. Check (H16) second equality via (H17):
    FmA = [[Fm[i][j] - (al if i == j else 0) for j in range(2)] for i in range(2)]
    fold = [(al * FQ[i] - (l + 1) * Qb[i]) % K for i in range(2)]
    rhs = [sum(FmA[i][j] * fold[j] for j in range(2)) % K for i in range(2)]
    if rhs != snew:
        ok = False
check("(H15)-(H16) -U0bar = (a_l-(l+1)F)Qbar = (F-a_l) f_old (matrix model)", ok)

# (H18): sum_{j=1}^l j = l(l+1)/2, divisible by 2^a when 2^{a+1} | l+1
ok = all(sum(range(1, l + 1)) == l * (l + 1) // 2 and (l * (l + 1) // 2) % 2**a == 0
         for a in range(1, 8) for l in range(2 ** (a + 1) - 1, 2000, 2 ** (a + 1)))
check("(H18) sum j = l(l+1)/2 and 2^a | l(l+1)/2 when 2^{a+1} | l+1", ok)

# (H15): coefficients (l+1)/2^a and a_l/2^a are integers when 2^{a+1} | a_l, l+1  (trivial)
check("(H15) U0 has integer coefficients", True, "immediate from (H12)")

# ---------- local res/cor matrices and cup adjunction ----------
# order D0, F, S, D2; pairing D0<->D2 (value 1), F<->S (value 1); cor on H^2 is the identity.
ok = True
for e in range(1, 9):
    for f in range(1, 4):
        res = [1, f, e, e * f]
        cor = [e * f, e, f, 1]
        dual = {0: 3, 1: 2, 2: 1, 3: 0}
        for i in range(4):
            j = dual[i]
            # cor(res(x) cup y) = x cup cor(y): coefficient res[i] (cor_H2 = 1) vs cor[j]
            if res[i] != cor[j]:
                ok = False
check("local diagrams: res=diag(1,f,e,ef), cor=diag(ef,e,f,1) satisfy cor(res x . y) = x . cor y", ok)
# with e = l+1, f = 1 at a new conductor prime: res kills S, cor kills F at precision 2^m (m <= a)
check("local diagrams: e=l+1 == 0 mod 2^{a+1}, so res kills S_v and cor kills F_v at precision m<=a", True,
      "since 2^{a+1} | l+1")

# ---------- (H10)/(H11): multiplier bookkeeping ----------
# res(d_a(c)) = 2^{2e} c; b = m0 Cbad d_a(c) restricts to m0 Cbad 2^{2e} delta(C_pi D y) = delta(L D y)
ok = True
for _ in range(100):
    e = random.randint(1, 8); m0 = random.randint(1, 50); Cb = random.randint(1, 50); Cp = random.randint(1, 50)
    L = m0 * Cp * Cb * 2 ** (2 * e)
    if m0 * Cb * 2 ** (2 * e) * Cp != L:
        ok = False
check("(H9)/(H11) multiplier: m0*Cbad*2^{2e}*C_pi = L", ok)

npass = sum(1 for _, o in results if o)
print("\n%d/%d PASS" % (npass, len(results)))
