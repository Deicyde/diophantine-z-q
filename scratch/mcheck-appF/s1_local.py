"""mcheck-appF s1: constants and local computations in App F, tex L8408-9405.

Pure Python. Each check prints PASS/FAIL with the tex line(s). Negative controls are
labelled NEG and must come out False (they are reported PASS when they fail as expected).
"""
import itertools
import random
from fractions import Fraction

random.seed(8408)
results = []


def check(name, ok, info=""):
    results.append((name, bool(ok)))
    print(("PASS " if ok else "FAIL ") + name + ((" : " + str(info)) if info else ""))


def neg(name, claim_value, info=""):
    """A negative control: the deliberately wrong claim must be False."""
    check("NEG " + name + " (wrong input must fail)", not claim_value, info)


def v2(x):
    x = abs(x)
    c = 0
    while x % 2 == 0:
        x //= 2
        c += 1
    return c


def legendre(a, p):
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def jacobi(a, n):
    assert n > 0 and n % 2 == 1
    a %= n
    r = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                r = -r
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            r = -r
        a %= n
    return r if n == 1 else 0


# ---------------- c0 = |GL_4(F_3)|, v2 c0 = 9 (L8414, L8580-8581) ----------------
def gl_order(n, q):
    r = 1
    for i in range(n):
        r *= q**n - q**i
    return r


c0 = gl_order(4, 3)
check("L8414 c0=|GL_4(F_3)|=24261120", c0 == 24261120, c0)
check("L8581 v2(c0)=9", v2(c0) == 9)
neg("v2(|GL_4(F_2)|)=9", v2(gl_order(4, 2)) == 9, v2(gl_order(4, 2)))
# unit groups of definite quaternion orders have order in {2,4,6,8,12,24}; all divide c0
check("L8589 |R_z^x| | c0 for |R_z^x| in {2,4,6,8,12,24}", all(c0 % w == 0 for w in (2, 4, 6, 8, 12, 24)))
check("L9390 c0/2 integral and v2(c0*2^w)=9+w (c_theta)", c0 % 2 == 0 and all(v2(c0 * 2**w) == 9 + w for w in range(8)))

# ---------------- Minkowski step (L8583-8588) ----------------
# (1+3^a A)^q with A nonzero mod 3: nonzero mod 3^{a+1} (q != 3) or mod 3^{a+2} (q = 3), a >= 1.
def matmul(A, B, mod):
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) % mod for j in range(n)] for i in range(n)]


def matpow(A, e, mod):
    n = len(A)
    R = [[int(i == j) for j in range(n)] for i in range(n)]
    for _ in range(e):
        R = matmul(R, A, mod)
    return R


ok = True
for trial in range(300):
    n = 4
    a = random.randint(1, 3)
    q = random.choice([2, 3, 5, 7])
    A = [[random.randint(0, 8) for _ in range(n)] for _ in range(n)]
    if all(A[i][j] % 3 == 0 for i in range(n) for j in range(n)):
        A[0][0] += 1
    mod = 3 ** (a + 2) if q == 3 else 3 ** (a + 1)
    M = [[(int(i == j) + 3**a * A[i][j]) % mod for j in range(n)] for i in range(n)]
    P = matpow(M, q, mod)
    I = [[int(i == j) for j in range(n)] for i in range(n)]
    if P == I:
        ok = False
check("L8583-8588 (1+3^aA)^q != 1 mod 3^{a+1} (q!=3) / 3^{a+2} (q=3)", ok)
# negative control: the same statement modulo 3 (instead of 3^{a+1}) is false
A = [[1, 0], [0, 0]]
M = [[1 + 3, 0], [0, 1]]
neg("Minkowski bound read modulo 3 only", matpow(M, 2, 3) != [[1, 0], [0, 1]])

# ---------------- nilpotent sign at p | m (L8538-8551) ----------------
def det2(g, p):
    return (g[0][0] * g[1][1] - g[0][1] * g[1][0]) % p


def conj(g, X, p):
    d = det2(g, p)
    di = pow(d, p - 2, p)
    gi = [[g[1][1] * di % p, -g[0][1] * di % p], [-g[1][0] * di % p, g[0][0] * di % p]]
    return matmul(matmul(g, X, p), gi, p)


for p in (3, 5, 7, 11):
    X0 = [[0, 1], [0, 0]]
    sign = {}
    good = True
    for a, b, c, d in itertools.product(range(p), repeat=4):
        g = [[a, b], [c, d]]
        if det2(g, p) == 0:
            continue
        N = tuple(map(tuple, conj(g, X0, p)))
        s = legendre(det2(g, p), p)
        if N in sign and sign[N] != s:
            good = False
        sign[N] = s
    # all nonzero nilpotents reached?
    nil = [(a, b, c) for a, b, c in itertools.product(range(p), repeat=3)
           if (a, b, c) != (0, 0, 0) and (-a * a - b * c) % p == 0]
    reached = all(((a, b), (c, (-a) % p)) in sign for a, b, c in nil)
    # scalar multiplication by u multiplies by (u/p)
    scal = all(sign[tuple(tuple(u * e % p for e in row) for row in N)] == legendre(u, p) * s
               for N, s in sign.items() for u in range(1, p))
    check("L8538-8551 eps_p well defined, all nilpotents, scaling (u/p), p=%d" % p, good and reached and scal)
# negative control: the 'sign' (a/p) of the top-left entry of g is not well defined
p = 5
sign = {}
good = True
for a, b, c, d in itertools.product(range(p), repeat=4):
    g = [[a, b], [c, d]]
    if det2(g, p) == 0 or a == 0:
        continue
    N = tuple(map(tuple, conj(g, [[0, 1], [0, 0]], p)))
    s = legendre(a, p)
    if N in sign and sign[N] != s:
        good = False
    sign[N] = s
neg("sign (g_11/p) well defined on nilpotent orbit", good)

# ---------------- residue line at ell_0 (L8553-8564) ----------------
def f_l2_elements(l):
    # F_{l^2} = F_l[i], i^2 = -1 (l = 3 mod 4)
    return [(a, b) for a in range(l) for b in range(l)]


ok = True
for l in (3, 7, 11, 19, 23, 31):
    # beta = i is trace zero: Frobenius (a,b)->(a,-b); beta^2 = -1 nonsquare
    beta2 = (-1) % l
    if legendre(beta2, l) != -1:
        ok = False
    for t in range(1, l):
        # Nrd(t beta) = N(t i) = t^2 ; Q_B = -x^2 = -(t i)^2 = t^2: nonzero square
        q = (-(t * t * beta2)) % l
        if legendre(q, l) != 1:
            ok = False
    if legendre(-1, l) != -1:
        ok = False
check("L8557-8563 beta^2 and -1 nonsquares, Q_B(x)=-t^2 beta^2 nonzero square (l=3 mod 4)", ok)
neg("same at l=13 (l=1 mod 4)", legendre(-1, 13) == -1)

# ---------------- existence of 2-power characters with alpha(-1)=-1 (L8501-8504, L8528-8530) ----
ok = True
for p in [3, 5, 7, 11, 13, 17, 41, 97, 113]:
    k = v2(p - 1)
    # alpha(g) = zeta_{2^k} for a generator g; -1 = g^{(p-1)/2}; alpha(-1) = zeta^{(p-1)/2} = -1 iff (p-1)/2 / 2^{k-1} odd
    ok &= ((p - 1) // 2) % 2**k == 2 ** (k - 1)
check("L8501 2-primary char of F_p^x sends -1 to -1", ok)
check("L8529 char mod 4 sends -1 to -1", (-1) % 4 == 3)

# ---------------- alpha(-1)=1 bookkeeping (L8584-8600) and root number twist (checked numerically in s4) ----
ok = True
for trial in range(2000):
    k = random.randint(0, 4)
    ws = [random.choice([1, -1]) for _ in range(k)]  # w_{p^e}
    chis = [random.choice([1, -1]) for _ in range(k)]  # chi_{h*}(p)
    es = [random.randint(1, 3) for _ in range(k)]
    prodN = 1
    for w, c, e in zip(ws, chis, es):
        prodN *= w * c**e
    wE = -1
    for w in ws:
        wE *= w
    chiN = 1
    for c, e in zip(chis, es):
        chiN *= c**e
    w_twist = wE * (-1) * chiN  # chi_{h*}(-N) = chi(-1) chi(N), chi(-1) = -1 for h* < 0
    # m = 3 mod 4: prod_{p|m}(-1/p) = (-1/m) = -1; ell0 = -1 mod 4: (-1/ell0) = -1
    m = random.choice([3, 7, 11, 15, 19, 23, 35, 39, 43])
    if m % 4 != 3:
        continue
    alpha_m1 = prodN * jacobi(-1 % m, m) * (-1)
    ok &= (w_twist == prodN) and (alpha_m1 == w_twist)
check("L8590-8600 alpha(-1) = prod w chi^e = w(E^{h*}) (formal)", ok)
# negative control: with m = 1 mod 4 the same bookkeeping would give alpha(-1) = -w(E^{h*})
neg("alpha(-1) = w(E^{h*}) when m = 5 (m = 1 mod 4)", 1 * jacobi(4, 5) * (-1) == 1)

# ---------------- 2-adic projectors (L8506-8526) ----------------
ok = True
for trial in range(2000):
    r = random.randrange(1, 2**20, 2)
    u = random.randrange(1, 2**20, 2)
    a, a2 = Fraction(1 + r, 2), Fraction(1 - r, 2)
    ok &= (a - a2 == r) and a.denominator == 1 and a2.denominator == 1
    # e_{ux} = u e_x + (1-u)/2 as affine map on eigenvalues: eigenvalue of e_x on r-line is (1+r)/2
    ok &= Fraction(1 + u * r, 2) == u * Fraction(1 + r, 2) + Fraction(1 - u, 2)
    # projector for eigenvalue r of x equals projector for eigenvalue ur of ux:
    # (x + r)/(2r) evaluated on the r-line is 1, on the (-r)-line is 0; same for (ux+ur)/(2ur)
    ok &= Fraction(r + r, 2 * r) == 1 and Fraction(-r + r, 2 * r) == 0
    ok &= Fraction(u * r + u * r, 2 * u * r) == 1 and Fraction(-u * r + u * r, 2 * u * r) == 0
check("L8507-8524 dyadic projectors: a-a'=r, e_{ux}=u e_x+(1-u)/2, selected root -> ur", ok)
# parities can switch: a=(1+r)/2 odd for r=1, even for u*r with u=3
check("L8524 eigenvalue parities of e_x can switch under x->ux", (1 + 1) // 2 % 2 == 1 and (1 + 3) // 2 % 2 == 0)
neg("e_{ux} = u e_x (no affine shift)", Fraction(1 + 3 * 5, 2) == 3 * Fraction(1 + 5, 2))

# idempotents of Z/2^e are 0,1 only (L8517)
check("L8517 idempotents of Z/2^e are {0,1}", all({x for x in range(2**e) if x * x % 2**e == x} == {0, 1} for e in range(1, 9)))
neg("idempotents of Z/6 are {0,1}", {x for x in range(6) if x * x % 6 == x} == {0, 1})

# ---------------- Atkin-Lehner normalizer reverses the selected root (L9321-9334) -----------
# Eichler order [[Z,Z],[p^e Z, Z]]; cyclic quotient = second coordinate mod p^e; x acts there by delta.
ok = True
for trial in range(500):
    p = random.choice([2, 3, 5, 7])
    e = random.randint(1, 3)
    q = p**e
    al, be, ga = (random.randint(-50, 50) for _ in range(3))
    x = [[Fraction(al), Fraction(be)], [Fraction(q * ga), Fraction(-al)]]
    W = [[Fraction(0), Fraction(1)], [Fraction(q), Fraction(0)]]
    Wi = [[Fraction(0), Fraction(1, q)], [Fraction(1), Fraction(0)]]
    y = [[sum(Wi[i][k] * sum(x[k][l] * W[l][j] for l in range(2)) for k in range(2)) for j in range(2)] for i in range(2)]
    inorder = all(t.denominator == 1 for row in y for t in row) and y[1][0] % q == 0
    # action on cyclic quotient: x acts by x[1][1] = -al, y acts by y[1][1]; reversed means sum = 0
    ok &= inorder and (y[1][1] + x[1][1]) == 0
check("L9321-9325 AL normalizer preserves Eichler order and reverses the root on the cyclic quotient", ok)
# negative control: claim that W preserves (rather than reverses) the root, on x = [[1,0],[0,-1]], q = 9
def al_conj(x, q):
    W = [[Fraction(0), Fraction(1)], [Fraction(q), Fraction(0)]]
    Wi = [[Fraction(0), Fraction(1, q)], [Fraction(1), Fraction(0)]]
    return [[sum(Wi[i][k] * sum(x[k][l] * W[l][j] for l in range(2)) for k in range(2)) for j in range(2)] for i in range(2)]


xx = [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(-1)]]
neg("AL normalizer preserves the root (x=diag(1,-1), q=9)", al_conj(xx, 9)[1][1] == xx[1][1], al_conj(xx, 9))

# ---------------- norm form of (-a,-b) on B^0, Gram determinants (L8691-8694, L8936-8941) ----------
def qmul(x, y, A, Bq):
    # quaternion (A,Bq): i^2=A, j^2=Bq, k=ij; x=(x0,x1,x2,x3)
    x0, x1, x2, x3 = x
    y0, y1, y2, y3 = y
    return (x0 * y0 + A * x1 * y1 + Bq * x2 * y2 - A * Bq * x3 * y3,
            x0 * y1 + x1 * y0 - Bq * x2 * y3 + Bq * x3 * y2,
            x0 * y2 + x2 * y0 + A * x1 * y3 - A * x3 * y1,
            x0 * y3 + x3 * y0 + x1 * y2 - x2 * y1)


ok = True
for trial in range(300):
    a, b = random.randint(1, 30), random.randint(1, 30)
    X, Y, Z = (random.randint(-9, 9) for _ in range(3))
    x = (0, X, Y, Z)
    xx = qmul(x, x, -a, -b)
    nrd = -xx[0]  # x^2 = -Nrd(x) for trace zero
    ok &= xx[1:] == (0, 0, 0) and nrd == a * X * X + b * Y * Y + a * b * Z * Z
check("L8692 Nrd on B^0 of (-a,-b) is aX^2+bY^2+abZ^2 and Q_B=-x^2", ok)
check("L8693 det of diag(a,b,ab) is (ab)^2 (square)", all((a * b * a * b) == (a * b) ** 2 for a in range(1, 9) for b in range(1, 9)))
# sl_2(Z_p), Q=-a^2-bc: Gram of B_Q has det 2 (unit at odd p) -> self-dual
G = [[-2, 0, 0], [0, 0, -1], [0, -1, 0]]
detG = (G[0][0] * (G[1][1] * G[2][2] - G[1][2] * G[2][1]) - G[0][1] * (G[1][0] * G[2][2] - G[1][2] * G[2][0])
        + G[0][2] * (G[1][0] * G[2][1] - G[1][1] * G[2][0]))
check("L8938 sl_2 Gram det = 2 (unit at odd p, so R_p^0 self-dual)", abs(detG) == 2, detG)
neg("sl_2 self-dual at p=2", detG % 2 != 0)

# ---------------- Fourier transform of 1_{Z_2^3} for Q0 (L8681-8687) ----------------
# B_{Q0}(x,y)=2x.y ; dual lattice of Z_2 is (1/2)Z_2 ; vol_{dx_Q}(Z_2^3) = |det 2I|_2^{1/2} = 2^{-3/2}
import cmath


def e2(t):
    # e_2(t) = exp(-2 pi i {t}_2) for t in Z[1/2]
    t = Fraction(t)
    frac = Fraction(t.numerator % t.denominator, t.denominator)
    return cmath.exp(-2j * cmath.pi * frac)


def ft1d(y, K=6):
    # integral over Z_2 of e_2(2 x y) dx, x mod 2^K, y in 2^-K Z
    return sum(e2(2 * x * y) for x in range(2**K)) / 2**K


ok = all(abs(ft1d(Fraction(k, 2)) - 1) < 1e-9 for k in range(-6, 7))
ok &= all(abs(ft1d(Fraction(k, 4))) < 1e-9 for k in range(-7, 8, 2))
ok &= abs((2 ** -0.5) ** 3 - 2 ** -1.5) < 1e-15
check("L8682-8684 F(1_{Z_2^3}) = 2^{-3/2} 1_{(1/2)Z_2^3} (per coordinate: support exactly (1/2)Z_2)", ok)
check("L8686 4 Q0((1/2)Z_2^3) in Z_2", all((4 * Fraction(a, 2) ** 2 + 4 * Fraction(b, 2) ** 2 + 4 * Fraction(c, 2) ** 2).denominator == 1
                                          for a in range(-3, 4) for b in range(-3, 4) for c in range(-3, 4)))
neg("depth one suffices at 2: 2 Q0((1/2)Z_2^3) in Z_2", all((2 * Fraction(a, 2) ** 2).denominator == 1 for a in range(-3, 4)))
# F^2 = id on 1_{Z_2^3}: 2^{-3/2} * vol((1/2)Z^3) * 1_{Z^3}, vol = 2^{-3/2} * 8
check("L8659 F_Q^2 = [x->-x] on 1_{Z_2^3} (measure bookkeeping)", abs(2 ** -1.5 * (2 ** -1.5 * 8) - 1) < 1e-12)

# ---------------- line counts and nonintegral neighbours (L9033-9050) ----------------
def lines(p):
    return [(1, t) for t in range(p)] + [(0, 1)]


def preserves(x, v, p):
    a, b, c, d = x
    w = ((a * v[0] + b * v[1]) % p, (c * v[0] + d * v[1]) % p)
    # w parallel to v
    return (w[0] * v[1] - w[1] * v[0]) % p == 0


ok = True
for p in (3, 5, 7, 11):
    for a, b, c in itertools.product(range(p), repeat=3):
        if (a, b, c) == (0, 0, 0):
            continue
        x = (a, b, c, (-a) % p)
        n = (-a * a - b * c) % p
        cnt = sum(preserves(x, v, p) for v in lines(p))
        ok &= cnt == 1 + legendre(-n, p)
    ok &= sum(preserves((0, 0, 0, 0), v, p) for v in lines(p)) == p + 1
check("L9035-9038 preserved lines = 1+(-n/p) for nonzero reduction (incl. nilpotent), p+1 for zero", ok)
neg("preserved lines = 1+(n/p)", all(sum(preserves((a, b, c, (-a) % 7), v, 7) for v in lines(7)) == 1 + legendre((-a * a - b * c), 7)
                                      for a, b, c in itertools.product(range(7), repeat=3) if (a, b, c) != (0, 0, 0)))


def nbr_order_contains(y, line, p, k):
    """Is y/p in End(Lambda_line), Lambda_line = preimage of line in Z_p^2? y given mod p^k."""
    # basis of Lambda: v=(v0,v1) lift of line, and p*w with w completing to a basis
    v = line
    w = (0, 1) if v[0] % p else (1, 0)
    g = [[v[0], p * w[0]], [v[1], p * w[1]]]  # columns basis of Lambda
    a, b, c, d = y
    Y = [[Fraction(a, p), Fraction(b, p)], [Fraction(c, p), Fraction(d, p)]]
    dg = Fraction(g[0][0] * g[1][1] - g[0][1] * g[1][0])
    gi = [[g[1][1] / dg, -g[0][1] / dg], [-g[1][0] / dg, g[0][0] / dg]]
    M = [[sum(gi[i][r] * sum(Y[r][s] * g[s][j] for s in range(2)) for r in range(2)) for j in range(2)] for i in range(2)]
    # p-integrality
    def integral(f):
        return f.denominator % p != 0
    return all(integral(t) for row in M for t in row)


ok = True
for p in (3, 5, 7):
    k = 2  # y/p integrality in a neighbour and p^2 | Q(y) depend only on y mod p^2
    for a, b, c in itertools.product(range(p**k), repeat=3):
        if a % p == 0 and b % p == 0 and c % p == 0:
            continue  # primitive only
        y = (a, b, c, -a)
        det = -a * a - b * c
        cnt = sum(nbr_order_contains(y, ln, p, k) for ln in lines(p))
        if det % (p * p) == 0:
            ok &= cnt == 1
        else:
            ok &= cnt == 0
    check("L9040-9050 primitive y: exactly one neighbour with y/p integral iff p^2 | Q(y), p=%d" % p, ok)
neg("exactly one neighbour iff p | Q(y)", all(
    (sum(nbr_order_contains((a, b, c, -a), ln, 3, 2) for ln in lines(3)) == 1) == ((-a * a - b * c) % 3 == 0)
    for a, b, c in itertools.product(range(9), repeat=3) if not (a % 3 == 0 and b % 3 == 0 and c % 3 == 0)))

# ---------------- recurrence algebra (L9052-9091) ----------------
# Given: s^{-1}H(p^2n) - H(n) [nonintegral] + (1+(-n/p))H(n) + p s H(n/p^2) [integral]
# total times s and the Brandt identity give H(p^2n)+s(-n/p)H(n)+p s^2 H(n/p^2) = s chi a_p H(n);
# with a(n)=H(mn), eta = s chi, psi = s (m/p): (O.6).
ok = True
for trial in range(3000):
    s = cmath.exp(2j * cmath.pi * random.randint(0, 15) / 16)  # 2-power root of unity, not quadratic in general
    chi = random.choice([1, -1])
    mp = random.choice([1, -1])  # (m/p)
    leg = random.choice([1, -1, 0])  # (-n/p)
    ap, p = random.randint(-30, 30), random.choice([3, 5, 7, 11, 13])
    Hn, Hnp = complex(random.randint(-99, 99)), complex(random.randint(-99, 99))
    # solve H(p^2 m n) from the H-recurrence at index mn: (-mn/p) = (m/p)(-n/p)
    Hp2 = s * chi * ap * Hn - s * (mp * leg) * Hn - p * s * s * Hnp
    eta, psi = s * chi, s * mp
    O6 = (eta * ap - psi * leg) * Hn - p * eta**2 * Hnp
    ok &= abs(Hp2 - O6) < 1e-9
    # sum of nonintegral and integral parts
    tot = (Hp2 / s - Hn) + (1 + mp * leg) * Hn + p * s * Hnp
    ok &= abs(tot - (Hp2 / s + mp * leg * Hn + p * s * Hnp)) < 1e-9
check("L9052-9091 recurrence algebra: H-identity => (O.6) with eta=s chi, psi=s(m/p), eta^2=s^2", ok)
# negative control: (O.6) with psi(p) in place of eta(p) in front of a_p, when (m/p) != chi(p)
s, chi, mp, leg, ap, p, Hn, Hnp = 1j, 1, -1, 1, 5, 7, 3.0, 2.0
Hp2 = s * chi * ap * Hn - s * (mp * leg) * Hn - p * s * s * Hnp
neg("(O.6) with psi(p) a_p", abs(Hp2 - ((s * mp * ap - s * mp * leg) * Hn - p * s * s * Hnp)) < 1e-9)

# ---------------- characters: psi/eta = chi_{-1}, parity (L8909-8916, L8984-8988) -----------
def kron(D, n):
    """Kronecker symbol (D/n), n > 0."""
    r = 1
    while n % 2 == 0:
        n //= 2
        if D % 2 == 0:
            return 0
        r *= 1 if D % 8 in (1, 7) else -1
    if n == 1:
        return r
    return r * jacobi(D % n, n)


ok = True
for m in (3, 7, 11, 15, 19, 23, 31, 35, 39, 43, 47, 51, 55, 59):
    for d in range(1, 400):
        if d % 2 == 0 or __import__("math").gcd(d, m) > 1:
            continue
        ok &= jacobi(m, d) * kron(-m, d) == kron(-4, d)  # (m/d)/chi_{h*}(d) = chi_{-1}(d), h* = -m
        ok &= jacobi(m, d) == kron(4 * m, d)  # (m/.) is the even character chi_{4m}
check("L8915 (m/d)/chi_{h*}(d) = chi_{-1}(d) and (m/.) = chi_{4m} (even) for m=3 mod 4", ok)
neg("(m/d)/chi_{h*}(d) = 1 (trivial)", all(jacobi(7, d) * kron(-7, d) == 1 for d in range(1, 60, 2) if d % 7))

# ---------------- biquadratic discriminant (L9197-9202) ----------------
def fund_disc(n):
    # n squarefree
    return n if n % 4 == 1 else 4 * n


def squarefree(n):
    n = abs(n)
    for q in range(2, int(n**0.5) + 1):
        if n % (q * q) == 0:
            return False
    return True


ok = True
for D in range(5, 300, 4):
    for h in range(-3, -200, -4):  # h = 1 mod 4 negative
        if not (squarefree(D) and squarefree(h)) or __import__("math").gcd(D, h) > 1 or h == -3:
            continue
        ok &= fund_disc(D) * fund_disc(h) * fund_disc(D * h) == (D * h) ** 2
check("L9199 disc Q(sqrt D, sqrt h*) = D h* (D h*) = (D h*)^2 (conductor-discriminant)", ok)
neg("same with D = 3 mod 4 (D=3, h=-7)", fund_disc(3) * fund_disc(-7) * fund_disc(-21) == (3 * 7) ** 2)

# ---------------- orientation count bookkeeping (L9152, L9300-9345, L9375-9387) --------------
ok = True
for w in range(0, 7):
    for Rz in (2, 4, 6, 8, 12, 24):
        per_orbit = Fraction(c0, Rz) * Fraction(Rz, 2)
        ok &= per_orbit == c0 // 2 and 2 ** (w + 1) * per_orbit == c0 * 2**w
check("L9375-9387 per orbit (c0/|R_z^x|)(|R_z^x|/2)=c0/2; 2^{w+1} tuples give c0 2^w", ok)
neg("stabilizer of order 4 (would give c0/4 per orbit)", Fraction(c0, 12) * Fraction(12, 4) == c0 // 2)
# (Dh*/l0) = (D/l0)(h*/l0) = -1 ; (m/l0) = (-1/l0)(h*/l0) = 1 with l0 = -1 mod 4
ok = True
for l0 in (3, 7, 11, 19, 23, 31, 43, 47):
    for h in (-7, -11, -15, -19, -23, -31, -35):
        if kron(h, l0) != -1:
            continue
        ok &= jacobi(-h, l0) == 1
        for D in range(1, 200, 4):
            if squarefree(D) and __import__("math").gcd(D, l0 * h) == 1 and kron(D, l0) == 1:
                ok &= kron(D * h, l0) == -1
check("L8437-8438, L9213-9214 (m/l0)=1 and (Dh*/l0)=-1 (inert) under (h*/l0)=-1, (D/l0)=1, l0=3 mod 4", ok)

npass = sum(ok for _, ok in results)
print("\n%d/%d PASS" % (npass, len(results)))
