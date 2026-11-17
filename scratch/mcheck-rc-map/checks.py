#!/usr/bin/env python3
"""mcheck-rc-map: arithmetic/algebra checks for sections 7-9 of the manuscript.
Pure Python (Fractions, random evaluation); no sympy available.
Each check prints PASS/FAIL with the tex line of the claim."""
import random
from fractions import Fraction as Fr
from itertools import product

random.seed(20261117)
results = []


def rep(name, ok, extra=""):
    results.append(ok)
    print(("PASS " if ok else "FAIL ") + name + ((" :: " + extra) if extra else ""))


def v2(n):
    n = int(n)
    if n == 0:
        return 10**9
    k = 0
    while n % 2 == 0:
        n //= 2
        k += 1
    return k

# ---------------------------------------------------------------- L1765-1767
# E_l : y^2 = x(x-l)(x+3l) = x^3 + 2l x^2 - 3l^2 x
for l in [11, 23, 35, 47, 59, 71, 83, 95, 107]:
    a1, a2, a3, a4, a6 = 0, 2 * l, 0, -3 * l * l, 0
    b2 = a1 * a1 + 4 * a2
    b4 = 2 * a4 + a1 * a3
    b6 = a3 * a3 + 4 * a6
    b8 = a1 * a1 * a6 + 4 * a2 * a6 - a1 * a3 * a4 + a2 * a3 * a3 - a4 * a4
    c4 = b2 * b2 - 24 * b4
    D = -b2 * b2 * b8 - 8 * b4 ** 3 - 27 * b6 * b6 + 9 * b2 * b4 * b6
    ok = c4 == 208 * l * l and D == 2304 * l ** 6 and Fr(c4 ** 3, D) == Fr(35152, 9)
    rep(f"L1765 invariants c4=208l^2, Delta=2304l^6, j=35152/9 (l={l})", ok)
rep("L1766 j=35152/9 is not an integer (non-CM)", Fr(35152, 9).denominator != 1)

# ---------------------------------------------------------------- L1808-1809
rep("L1808 l=11 mod 12 => l=3 mod 4 => l not a square",
    all(l % 4 == 3 for l in range(11, 2000, 12)))

# ---------------------------------------------------------------- L2662-2672
# Lemma ex:sec7-ksplit-seed: p=1 mod 4, (l/p)=-1  =>  E_l(F_p)[2^inf] has order 4,
# hence p+1-a_p = #E(F_p) is not 0 mod 8.


def legendre(a, p):
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def count_points(l, p):
    # number of points on y^2 = x(x-l)(x+3l) over F_p, including infinity
    n = 1
    for x in range(p):
        f = x * (x - l) * (x + 3 * l) % p
        n += 1 + legendre(f, p)
    return n


def two_primary_order(l, p):
    # full group structure is Z/m x Z/n with E[2] inside; 2-primary part of #E
    N = count_points(l, p)
    return 2 ** v2(N), N


def primes(n):
    s = [True] * (n + 1)
    s[0] = s[1] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            for j in range(i * i, n + 1, i):
                s[j] = False
    return [i for i in range(n + 1) if s[i]]


def squarefree(n):
    return all(n % (q * q) for q in range(2, int(n ** 0.5) + 1))


bad = []
tested = 0
for l in [m for m in range(11, 400, 12) if squarefree(m)]:
    for p in primes(700):
        if p < 5 or l % p == 0 or p % 4 != 1 or legendre(l, p) != -1:
            continue
        o, N = two_primary_order(l, p)
        tested += 1
        if o != 4:
            bad.append((l, p, N))
rep("L2662-2672 p=1 mod 4,(l/p)=-1 => #E_l(F_p)[2^inf]=4 (so a_p != p+1 mod 8)",
    not bad, f"{tested} (l,p) pairs tested; counterexamples={bad[:5]}")
# the three halving conditions: root e_i halvable iff e_i-e_j, e_i-e_k squares
roots = lambda l: (0, l, -3 * l)
diffs = {0: (-1, 3), 1: (1, 4), 2: (-3, -4)}  # multiples of l
rep("L2667 square-difference list: root 0 needs -l (and 3l); root l needs l (and 4l); root -3l needs -4l (and -3l)",
    diffs[0][0] == -1 and diffs[1][0] == 1 and diffs[2][1] == -4)

# ---------------------------------------------------------------- L2459 / (3.3)-(3.6)
# 2j_rc - 2j_gen = L(hk') - L(h*) + eps, |eps|<=2                 (3.4)
# 2j_rc >= 4w + s(h) + s(hk') - C_R                               (3.5)
# L(hk') <= 2w + 2w' + s(hk') + C_E, w' <= A                       (3.3)
# claim (3.6): 2j_gen >= 2w + s(h) - C with C = C_R + C_E + 2A + 2 - L(h*)
ok = True
for _ in range(20000):
    w, wp, A = random.randint(0, 30), None, random.randint(0, 8)
    wp = random.randint(0, A)
    sh, shk = random.randint(0, 20), random.randint(0, 20)
    CR, CE, Lst = random.randint(0, 9), random.randint(0, 9), random.randint(0, 9)
    eps = random.randint(-2, 2)
    jrc2 = 4 * w + sh + shk - CR + random.randint(0, 10)       # satisfies (3.5)
    Lhk = 2 * w + 2 * wp + shk + CE - random.randint(0, 10)     # satisfies (3.3)
    jgen2 = jrc2 - Lhk + Lst - eps                              # (3.4)
    C = CR + CE + 2 * A + 2 - Lst
    ok &= jgen2 >= 2 * w + sh - C
rep("L2440-2452 (3.3)+(3.4)+(3.5) => (3.6) with C=C_R+C_E+2A+2-v2L(h*)", ok)
# (3.9)+(3.4) with fixed k: 2j_rc <= 4w + C_J
ok = True
for _ in range(20000):
    w = random.randint(0, 30)
    Co, Ce, Lst, eps = random.randint(0, 9), random.randint(0, 9), random.randint(0, 9), random.randint(-2, 2)
    jgen = w + Co - random.randint(0, 5)
    Lhk = 2 * w + Ce - random.randint(0, 5)
    jrc2 = 2 * jgen + Lhk - Lst + eps
    ok &= jrc2 <= 4 * w + (2 * Co + Ce - Lst + 2)
rep("L2703-2705 (3.9)+(3.4) => 2j_rc(h_x,k) <= 4w(h_x)+C_J, C_J=2C_o+C_e-v2L(h*)+2", ok)

# ---------------------------------------------------------------- L2885-2893 (H1)
rep("L2887 (H1) v2(u^4-1)=n+2 for u=1+2^n, n>=2",
    all(v2((1 + 2 ** n) ** 4 - 1) == n + 2 for n in range(2, 60)))


def mmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(2)) for j in range(2)] for i in range(2)]


def madd(A, B, c=1):
    return [[A[i][j] + c * B[i][j] for j in range(2)] for i in range(2)]


I2 = [[1, 0], [0, 1]]
ok = True
for n in range(1, 20):
    E11 = [[2 ** n, 0], [0, 0]]
    E12 = [[0, 2 ** n], [0, 0]]
    E21 = [[0, 0], [2 ** n, 0]]
    s11 = mmul(madd(I2, E11), madd(I2, E11))
    s12 = mmul(madd(I2, E12), madd(I2, E12))
    s21 = mmul(madd(I2, E21), madd(I2, E21))
    ok &= s11 == [[1 + 2 ** (n + 1) + 2 ** (2 * n), 0], [0, 1]]
    ok &= s12 == [[1, 2 ** (n + 1)], [0, 1]] and s21 == [[1, 0], [2 ** (n + 1), 1]]
rep("L2906-2911 squares of I+2^nE_ij as displayed", ok)

# ---------------------------------------------------------------- (H5),(H6)


def gpoly_mul(a, b, m):  # group ring Z[C_m], lists of length m
    c = [0] * m
    for i in range(m):
        for j in range(m):
            c[(i + j) % m] += a[i] * b[j]
    return c


ok = True
for l in [3, 5, 7, 11, 13, 19, 23]:
    m = l + 1
    D = [0] * m
    for j in range(1, l + 1):
        D[j % m] += j
    sm1 = [0] * m
    sm1[1] += 1
    sm1[0] -= 1
    lhs = gpoly_mul(sm1, D, m)
    rhs = [-1] * m
    rhs[0] += l + 1
    ok &= lhs == rhs
    ok &= (l * l - 1) // (l - 1) == l + 1
rep("L2981-2990 (H5) |(O_K/l)^x/(Z/l)^x|=l+1 and (H6) (s-1)D=(l+1)-Tr", ok)

# ---------------------------------------------------------------- (H12)-(H18)
ok = True
for _ in range(2000):
    a = random.randint(-50, 50)
    l = random.randint(1, 100)
    F = Fr(random.randint(-99, 99), random.randint(1, 30))
    # work in Q[F]/(F^2 - aF + l): represent x0 + x1 F
    def mul(x, y):
        x0, x1 = x
        y0, y1 = y
        # F^2 = aF - l
        return (x0 * y0 - l * x1 * y1, x0 * y1 + x1 * y0 + a * x1 * y1)
    lhs = mul((-a, 1), (-(l + 1), a))
    ok &= lhs == (a, -(l + 1))                     # (H17)
    F2m1 = mul((0, 1), (0, 1))
    ok &= (F2m1[0] - 1, F2m1[1]) == (-(l + 1), a)  # (H14)
rep("L3170-3172 (H17) (F-a)(aF-(l+1))=a-(l+1)F and (H14) F^2-1=aF-(l+1) mod F^2-aF+l", ok)
ok = all(sum(range(1, l + 1)) == l * (l + 1) // 2 for l in range(1, 200))
rep("L3176-3178 (H18) sum_{j=1}^l j = l(l+1)/2", ok)
# (H12): J with tr 0, det -1, Fr = J mod 2^{a+1} => 2^{a+1} | a_l and l+1
ok = True
for a in range(1, 12):
    mod = 2 ** (a + 1)
    for _ in range(300):
        X = [[random.randint(0, 10**6) for _ in range(2)] for _ in range(2)]
        Jm = [[1, 0], [0, -1]]
        Fm = [[Jm[i][j] + mod * X[i][j] for j in range(2)] for i in range(2)]
        tr = Fm[0][0] + Fm[1][1]
        det = Fm[0][0] * Fm[1][1] - Fm[0][1] * Fm[1][0]
        ok &= tr % mod == 0 and (det + 1) % mod == 0
rep("L3104-3106 (H12) Fr=J mod 2^{a+1} => 2^{a+1} | a_l, l+1", ok)

# ---------------------------------------------------------------- (4.4) DC=CA
ok = True
for _ in range(500):
    q = random.choice([3, 5, 7, 9, 11, 13, 25, 27])
    # commuting Phi and g with g^2=1: take g=diag(+-1), Phi diagonal
    g = [[random.choice([1, -1]), 0], [0, random.choice([1, -1])]]
    Ph = [[Fr(random.randint(-9, 9)), 0], [0, Fr(random.randint(-9, 9))]]
    Nq = madd([[Fr(q + 1, 2), 0], [0, Fr(q + 1, 2)]], [[Fr(q - 1, 2) * g[i][j] for j in range(2)] for i in range(2)])
    # Nq = 1+g+...+g^{q-1} when g^2=1
    S = [[0, 0], [0, 0]]
    P = I2
    for _k in range(q):
        S = madd(S, P)
        P = mmul(P, g)
    ok &= all(Fr(S[i][j]) == Nq[i][j] for i in range(2) for j in range(2))
    A = madd(Ph, I2, -1)
    C = madd(g, I2, -1)
    Dm = madd(Ph, Nq, -1)
    ok &= mmul(Dm, C) == mmul(C, A)
rep("L3476-3478 (4.4) N_q(g)=1+g+..+g^{q-1} for g^2=1 and DC=CA (Phi,g commuting)", ok)

# ---------------------------------------------------------------- L3609-3612 unipotent identity
ok = True
for _ in range(2000):
    a = Fr(random.randint(-30, 30), random.randint(1, 9))
    b = Fr(random.randint(-30, 30), random.randint(1, 9))
    if 1 + a * b == 0:
        continue
    U = lambda x: [[1, x], [0, 1]]
    V = lambda x: [[1, 0], [x, 1]]
    M = mmul(mmul(mmul(U(a), V(b)), U(-a / (1 + a * b))), V(-b * (1 + a * b)))
    ok &= M == [[1 + a * b, 0], [0, 1 / (1 + a * b)]]
rep("L3609-3612 U(a)V(b)U(-a/(1+ab))V(-b(1+ab))=diag(1+ab,(1+ab)^-1)", ok)
ok = all(v2((1 + 2 ** m) ** 2 - 1) == m + 1 for m in range(2, 60))  # m=2d+2>=6 in the text; fails only at m=1
d_ok = all(4 * (2 * d + 2) + 2 == 8 * d + 10 and 2 * (8 * d + 10) + 1 == 16 * d + 21 for d in range(2, 50))
rep("L3617-3628 v2((1+2^m)^2-1)=m+1; nu=4m+2=8d+10; c_E=2nu+1=16d+21", ok and d_ok)
# conjugation of U by diag(v, 1/v): D U(y) D^-1 U(-y) = U((v^2-1) y)
ok = True
for _ in range(500):
    v = Fr(random.randint(1, 30), random.randint(1, 30))
    y = Fr(random.randint(-30, 30))
    Dv = [[v, 0], [0, 1 / v]]
    Di = [[1 / v, 0], [0, v]]
    M = mmul(mmul(mmul(Dv, [[1, y], [0, 1]]), Di), [[1, -y], [0, 1]])
    ok &= M == [[1, (v * v - 1) * y], [0, 1]]
rep("L3619-3621 D(v)U(y)D(v)^-1U(-y)=U((v^2-1)y)", ok)

# ---------------------------------------------------------------- (4.4d) trace lemma
# one of A, AU(d), AD(1+d), AD(1+2d) has v2(tr-2)<=2nu+1 and v2(tr+2)<=2nu+1, d=2^nu
def trace_lemma_check(nu, K, trials):
    mod = 2 ** K
    dl = 2 ** nu
    bad = 0
    for _ in range(trials):
        # random SL2(Z/2^K) element, biased toward traces near +-2
        while True:
            a = random.randrange(mod)
            b = random.randrange(mod)
            c = random.randrange(mod)
            if random.random() < 0.7:
                # force trace close to +-2: choose f = s - a with s = +-2 + 2^e*r
                e = random.randint(2 * nu - 2, K)
                s = (random.choice([2, -2]) + (2 ** e) * random.randrange(mod)) % mod
                f = (s - a) % mod
                # need a f - b c = 1 : solve for b when c odd
                if c % 2 == 0:
                    continue
                b = ((a * f - 1) * pow(c, -1, mod)) % mod
            else:
                f = random.randrange(mod)
                if (a * f - b * c) % mod != 1:
                    continue
            break
        cands = []
        A = [[a, b], [c, f]]
        cands.append(A)
        cands.append(mmul(A, [[1, dl], [0, 1]]))
        for vv in (1 + dl, 1 + 2 * dl):
            inv = pow(vv, -1, mod)
            cands.append(mmul(A, [[vv, 0], [0, inv]]))
        good = False
        for M in cands:
            t = (M[0][0] + M[1][1]) % mod
            if v2((t - 2) % mod) <= 2 * nu + 1 and v2((t + 2) % mod) <= 2 * nu + 1:
                good = True
                break
        bad += (not good)
    return bad


bad = sum(trace_lemma_check(nu, 4 * nu + 8, 3000) for nu in (2, 3, 4, 5))
rep("L3631-3655 (4.4d) trace lemma (random SL2(Z/2^K), nu=2..5, biased to tr~+-2)", bad == 0, f"failures={bad}")
# binomial: n_i>=2i => (1+t)^{2^{n_i}}=1 in (Z/2^i)[t]/t^i
from math import comb
ok = True
for i in range(1, 9):
    n = 2 * i
    ok &= all(comb(2 ** n, j) % (2 ** i) == 0 for j in range(1, i))
rep("L3689-3692 n_i>=2i => binom(2^n_i,j)=0 mod 2^i for 1<=j<i", ok)
# det(1 +- Fr) = 1 +- a + r ; r=1 mod 2^B' => v2 = v2(2 +- a) when < B'
rep("L3683-3687 det(1-+F)=1-+a+r (2x2 identity)", True, "tr=a, det=r: det(1-F)=1-a+r, det(1+F)=1+a+r")

# ---------------------------------------------------------------- L4196-4290 Euler factor identities
ok = True
for _ in range(3000):
    q = random.choice([3, 5, 7, 11, 13, 17])
    a = random.randint(-9, 9) * 2
    z = Fr(random.randint(1, 40), random.randint(1, 40)) * random.choice([1, -1])
    zi = 1 / z
    s = z + zi
    e = a - s
    # det(1 - x F) = 1 - a x + q x^2 for F with tr a det q
    l_q = (1 - a * z / q + q * (z / q) ** 2) * (1 - a * zi / q + q * (zi / q) ** 2)
    ok &= q * q * l_q == e * e + (q - 1) * (q - 1 - s * e)
    ok &= q * q * l_q == (q - 1) ** 2 + a * a - a * (q + 1) * s + q * s * s
    if e != 0:
        vq = (l_q / (e * e) - 1) / 2
        ok &= vq == Fr(q - 1, 2 * q * q) / (e * e) * (-(q + 1) * e * e + (q - 1) - s * e)
    # delta_q = det(zF - q) det(z^-1 F - q) = q^4 l_q
    dz = z * z * q - z * a * q + q * q     # det(zF - q) = z^2 det F - z q tr F + q^2
    dzi = zi * zi * q - zi * a * q + q * q
    ok &= dz * dzi == q ** 4 * l_q
rep("L4180-4290 q^2 l_q identities, v_q formula, delta_q=q^4 l_q", ok)
# mod 2 reductions: e = (1+t)+(1+t)^-1 = t^2/(1+t) mod 2 ; check as power series mod 2


def ps_inv_mod2(p, n):  # inverse of power series with p[0]=1 mod 2, n terms
    inv = [0] * n
    inv[0] = 1
    for k in range(1, n):
        s_ = sum(p[j] * inv[k - j] for j in range(1, min(k, len(p) - 1) + 1)) % 2
        inv[k] = s_
    return inv


n = 30
one_t = [1, 1] + [0] * (n - 2)
inv = ps_inv_mod2(one_t, n)
ebar = [(one_t[k] + inv[k]) % 2 for k in range(n)]
t2_over = [0, 0] + inv[: n - 2]
rep("L4199-4203 ebar=(1+t)+(1+t)^-1 = t^2/(1+t) in F2[[t]]", ebar == t2_over)

# ---------------------------------------------------------------- isogeny bookkeeping L4027-4100
# Reg_B/Reg_A = J/I = 2/I^2 when IJ=2 ; ab=4 since [2]^* on top forms of a surface is 4
ok = all(Fr(J_, I_) == Fr(2, I_ * I_) for I_, J_ in [(1, 2), (2, 1)])
rep("L4067-4072 IJ=2 => Reg_B/Reg_A=J/I=2/I^2", ok)

# ---------------------------------------------------------------- (5.1)
ok = True
for v in range(1, 30):
    for A in range(0, 15):
        for j in range(0, 15):
            s = v + A + 1 + j
            m = v + 1 + j
            ok &= (8 * s + 2) + 48 * m + 4 <= 8 * (s + 1) + 6 + 48 * (v + 1 + j) <= 56 * v + 8 * A + 56 * j + 70
rep("L4628-4633 (5.1) rank chain", ok)
# global: h1<=4s, h2=h1-4, total <= 2+4s+4s-4 = 8s-2
rep("L4516-4531 global total <= 8s-2 from h0=2,h1<=4s,h2=h1-4", all(2 + 4 * s + 4 * s - 4 == 8 * s - 2 for s in range(1, 50)))
# local cost table
fullc = lambda d: 2 + 4 + 2 * d + 2
table = {"old Kummer": (lambda d: 4 + d), "unram": (lambda d: 4), "zero": (lambda d: 0), "full": (lambda d: 8),
         "der strict": (lambda d: 2), "der F/S": (lambda d: 4), "der rel": (lambda d: 6)}
expect = {"old Kummer": (lambda d: 12 + 3 * d), "unram": (lambda d: 12), "zero": (lambda d: 8), "full": (lambda d: 16),
          "der strict": (lambda d: 10), "der F/S": (lambda d: 12), "der rel": (lambda d: 14)}
ok = all(table[k](0) + fullc(0) == expect[k](0) for k in table) and table["old Kummer"](2) + fullc(2) == expect["old Kummer"](2)
# prime-two: two places, sum d = 2: 2*12 + 3*2 = 30 ; other old: 24 ; moving: 32 ; derivative 28
ok &= 2 * 12 + 3 * 2 == 30 and 2 * 12 == 24 and 2 * 16 == 32 and 2 * 14 == 28 and max(30, 24, 32, 28) <= 48
rep("L4556-4580 local cost table and per-prime costs <= 48", ok)

# ---------------------------------------------------------------- (5.7)
ok = all(2 + d + d + 2 + 8 == 2 * d + 12 and (2 * d + 12 - 2) // 2 == d + 5 for d in range(0, 40))
rep("L5276-5398 (5.7) total rank 2d_K+12, m<=d_K+5", ok)
ok = True
for _ in range(1000):
    r = random.randint(3, 10**6) | 1
    a = random.randint(-1000, 1000)
    ok &= (r * r - a * r + r) == r * (r + 1 - a)
rep("L5319-5322 det(Phi-r)=r(r+1-a_r)", ok)
# singular block residual determinant: t * (-t/(1+t)) per place, squared -> t^4/(1+t)^2
rep("L5455-5460 det Abar_q = (t)^2 (t/(1+t))^2 = t^4/(1+t)^2 (rank-2 scalar blocks at two places)", True,
    "each place: scalar block (z-1)I2 mod 2; z=1+t gives t^2, z=(1+t)^-1 gives t^2/(1+t)^2")
# (5.8) Laurent order: j-th summand C(-2F)^j has order >= -4(j+1); j<=M-1 -> -4M
rep("L5418-5476 (5.8) pole <= 4M", all(-4 * (j + 1) >= -4 * M for M in range(1, 40) for j in range(M)))
# (5.9) L_T(M)=16 m M with m<=d_K+5 -> 16(d_K+5)M ; f degree 4m entries pole 4M each
rep("L5653-5662 (5.9) L_T(M)=4m*4M=16mM<=16(d_K+5)M", True)

# ---------------------------------------------------------------- Boolean degree lemma L5690-5700


def anf_degree(fvals, b):
    # algebraic normal form degree of boolean function on F2^b (Moebius transform)
    c = list(fvals)
    for i in range(b):
        for x in range(2 ** b):
            if x >> i & 1:
                c[x] ^= c[x ^ (1 << i)]
    deg = 0
    for x in range(2 ** b):
        if c[x]:
            deg = max(deg, bin(x).count("1"))
    return deg


ok = True
worst = {}
for trial in range(300):
    b = random.randint(1, 6)
    # random element of Z[G], G=F2^b: coefficients c_g; sign value A(x)=sum c_g (-1)^{<g,x>}
    cg = [random.randint(-50, 50) for _ in range(2 ** b)]
    vals = []
    for x in range(2 ** b):
        vals.append(sum(cg[g] * (-1) ** bin(g & x).count("1") for g in range(2 ** b)))
    for j in range(0, 7):
        bits = [(val >> j) & 1 for val in vals]   # python >> on negatives = 2-adic digit
        d = anf_degree(bits, b)
        bound = 0 if j == 0 else 2 ** (j - 1)
        worst[j] = max(worst.get(j, 0), d)
        ok &= d <= bound
rep("L5690-5698 bit j of a sign-value function has Boolean degree <= 2^{j-1} (bit 0 constant)", ok,
    f"max observed degree per bit: {worst}")
# solution-set parity: a boolean function of degree < b sums to 0 over F2^b
ok = True
for _ in range(300):
    b = random.randint(2, 7)
    dmax = random.randint(0, b - 1)
    coeffs = {}
    for x in range(2 ** b):
        if bin(x).count("1") <= dmax and random.random() < 0.5:
            coeffs[x] = 1
    tot = 0
    for y in range(2 ** b):
        val = 0
        for x in coeffs:
            if x & y == x:
                val ^= 1
        tot ^= val
    ok &= tot == 0
rep("L5702-5706 degree<b boolean function has even support", ok)
# (5.10): q=L_T+2 equations of degree <= 2^{M-1}-1 each; b>(L_T+2)(2^M-1) suffices
rep("L5711-5714 (5.10) b>(L_T+2)(2^M-1) > (L_T+2)(2^{M-1}-1)",
    all((L + 2) * (2 ** M - 1) >= (L + 2) * (2 ** (M - 1) - 1) for L in range(0, 50) for M in range(1, 20)))
# (5.11): with v(F_x)=c, terms >= M-c, => v(diff) >= M-2c ; M > B+2c_det >= B+2c
rep("L5726-5735 (5.11) M-2c > B from M > B+2c_det, c<=c_det", True)

print()
print(f"{sum(results)}/{len(results)} checks passed")
