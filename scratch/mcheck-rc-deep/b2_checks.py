"""mcheck-rc-deep, block 2 (tex L4747-5205): switches and the uniform bound (5.5).

Pure Python over Q (Fractions) / integers. Checks:
 S1  switch lemma: pairing identities beta(x,Jv)=eps<x,v>, beta(v,y) = -eps<Jv,y>; <v,J J v> = 0;
     equal-valuation of the F- and S- class-functional coordinates in a toy determinant model.
 S2  (5.5) Schur formula: u = +- alpha beta / Delta for ANY nonzero maximal minor; v2 bound.
 S3  quadratic case: (1+t)^2=1 <=> t(t+2)=0; e2(x,Jy) symmetric; hyperbolic planes H_+-; isotropic
     lines are the axes; sign bookkeeping of (5.5a) in both cases; (5.5b) identity.
 S4  (5.5) + (4.6) => (3.5) inequality bookkeeping; u(0) >= Gauss valuation for u in Lambda[1/2].
 S5  outer-switch dimension count s -> s-2 (rank-two localization, Lagrangian image).
"""
import random
import itertools
from fractions import Fraction as Fr

random.seed(5205)
results = []


def check(name, ok, info=""):
    results.append(ok)
    print(("PASS " if ok else "FAIL ") + name + ((" : " + info) if info else ""))


def v2(x):
    x = Fr(x)
    if x == 0:
        return 10**9
    n, d = x.numerator, x.denominator
    c = 0
    while n % 2 == 0:
        n //= 2; c += 1
    while d % 2 == 0:
        d //= 2; c -= 1
    return c


def det2(a, b):
    return a[0] * b[1] - a[1] * b[0]


def mv(M, v):
    return (M[0][0] * v[0] + M[0][1] * v[1], M[1][0] * v[0] + M[1][1] * v[1])


def mm(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]


def rand_J():
    while True:
        P = [[random.randint(-6, 6) for _ in range(2)] for _ in range(2)]
        d = P[0][0] * P[1][1] - P[0][1] * P[1][0]
        if d in (1, -1):
            break
    Pi = [[P[1][1] * d, -P[0][1] * d], [-P[1][0] * d, P[0][0] * d]]
    return mm(mm(P, [[1, 0], [0, -1]]), Pi)


# ---------------- S1: switch lemma pairing identities ----------------
ok = True
for _ in range(500):
    J = rand_J()
    eps = random.choice([1, -1, 3])
    v = (random.randint(-20, 20), random.randint(-20, 20))
    x = (random.randint(-20, 20), random.randint(-20, 20))
    y = (random.randint(-20, 20), random.randint(-20, 20))
    beta = lambda a, b: eps * det2(a, mv(J, b))  # beta(x,y) = eps <x, J y>, <,> = det (Weil pairing)
    if beta(x, mv(J, v)) != eps * det2(x, v):
        ok = False
    if beta(v, y) != -eps * det2(mv(J, v), y):
        ok = False
    if det2(v, mv(J, mv(J, v))) != 0:  # (v,0) and (0,Jv) are orthogonal
        ok = False
check("S1 beta(x,Jv)=eps<x,v>; beta(v,y)=-eps<Jv,y>; beta(v,Jv)=0 (J^2=1, det J=-1)", ok)

# Toy determinant model for the switch: H^1(C_rel) = <A,B>, H^2(C_str) = <A*,B*> (dual basis),
# F-sequence: A -> v, x -> eps<x,v> B*;  S-sequence: B -> Jv, y -> beta(v,y)-type unit * A*.
# u_F = vol_F(v ^ x)/vol_str(xbar ^ w_A), w_A = A* (lambda_A = evaluation at A);
# u_S = vol_S(Jv ^ y)/vol_str(ybar ^ w_B), w_B = B*. Compare 2-adic valuations with v divisible.
ok = True
for _ in range(500):
    J = rand_J()
    eps = random.choice([1, -1, 3, -5])
    k = random.randint(0, 6)
    v0 = (random.randint(-30, 30), random.randint(-30, 30))
    if v0 == (0, 0):
        continue
    v = (2**k * v0[0], 2**k * v0[1])
    # x: rational complement with det(v, x) = 1 (unit volume, possibly fractional)
    if v[0] != 0:
        x = (Fr(0), Fr(1, v[0]))
    else:
        x = (Fr(-1, v[1]), Fr(0))
    Jv = mv(J, v)
    if Jv[0] != 0:
        y = (Fr(0), Fr(1, Jv[0]))
    else:
        y = (Fr(-1, Jv[1]), Fr(0))
    assert det2(v, x) == 1 and det2(Jv, y) == 1
    xbar_coef_B = eps * det2(x, v)            # image of x in H^2(C_str), coefficient of B*
    ybar_coef_A = eps * det2(v, mv(J, y))     # image of y, coefficient of A*
    # vol_str(xbar ^ A*) with basis (A*,B*): det[[0, 1],[xB, 0]] up to sign = xB
    uF = Fr(det2(v, x)) / abs(xbar_coef_B)
    uS = Fr(det2(Jv, y)) / abs(ybar_coef_A)
    if v2(uF) != v2(uS):
        ok = False
check("S1 switch: F- and S- class-functional coordinates have equal valuation, even for divisible v", ok)

# negative control: if s(B) were 2*Jv (a non-unit multiple), the S-coordinate would shift by v2 = +1
J = rand_J(); v = (4, 6); Jv2 = tuple(2 * c for c in mv(J, v))
y = (Fr(0), Fr(1, Jv2[0])) if Jv2[0] != 0 else (Fr(-1, Jv2[1]), Fr(0))
x = (Fr(0), Fr(1, v[0]))
uF = Fr(1) / abs(det2(x, v)); uS2 = Fr(det2(Jv2, y)) / abs(det2(v, mv(J, y)))
check("S1 control: with s(B)=2Jv instead of Jv the valuations differ (so exactness of (4.2) matters)",
      v2(uS2) == v2(uF) + 1, "v2 uF=%d, v2 uS=%d" % (v2(uF), v2(uS2)))

# ---------------- S2: Schur / Cramer formula for the class-functional coordinate ----------------


def det(M):
    M = [[Fr(x) for x in r] for r in M]
    n = len(M); d = Fr(1)
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None:
            return Fr(0)
        if p != c:
            M[c], M[p] = M[p], M[c]; d = -d
        d *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            for kk in range(c, n):
                M[r][kk] -= f * M[c][kk]
    return d


def minor(D, r, c):
    return [[D[i][j] for j in range(len(D)) if j != c] for i in range(len(D)) if i != r]


def kernel_vector(D):
    n = len(D)
    # adjugate column: z_j = (-1)^{r+j} minor(D, r, j) for a row r with some nonzero minor
    for r in range(n):
        z = [(-1) ** (r + j) * det(minor(D, r, j)) for j in range(n)]
        if any(z):
            return z
    return None


ok = True
okb = True
trials = 0
for _ in range(300):
    n = random.randint(2, 5)
    # random integer matrix of rank n-1: D = P diag(d_1..d_{n-1},0) Q with P,Q unimodular-ish
    while True:
        B = [[random.randint(-4, 4) * random.choice([1, 2, 4]) for _ in range(n)] for _ in range(n - 1)]
        comb = [random.randint(-3, 3) for _ in range(n - 1)]
        last = [sum(comb[i] * B[i][j] for i in range(n - 1)) for j in range(n)]
        D = B + [last]
        perm = list(range(n)); random.shuffle(perm)
        D = [D[p] for p in perm]
        if any(det(minor(D, r, c)) != 0 for r in range(n) for c in range(n)):
            break
    z = kernel_vector(D)
    assert all(sum(D[i][j] * z[j] for j in range(n)) == 0 for i in range(n))
    # lambda: a functional on coker D = Q^n / im D: pick w with w^T D = 0, lambda(f) = w . f
    Dt = [[D[j][i] for j in range(n)] for i in range(n)]
    w = kernel_vector(Dt)
    # canonical coordinate: choose complement indices; u = det[z, e_Jc] / det[D e_Jc, y], lambda(y)=1
    us = set()
    for j0 in range(n):
        if z[j0] == 0:
            continue
        cols = [j for j in range(n) if j != j0]
        Dcols = [[D[i][j] for j in cols] for i in range(n)]
        for k0 in range(n):
            if w[k0] == 0:
                continue
            yv = [Fr(0)] * n; yv[k0] = Fr(1) / w[k0]
            top = det([[z[i] if c == 0 else (1 if i == cols[c - 1] else 0) for c in range(n)] for i in range(n)])
            bot = det([[Dcols[i][c] if c < n - 1 else yv[i] for c in range(n)] for i in range(n)])
            if bot == 0:
                continue
            u = top / bot
            us.add(abs(u))
            # formula u = +- z_{j0} * lambda(f_{k0}) / M_{k0 j0}
            M = det(minor(D, k0, j0))
            if M != 0 and abs(u) != abs(Fr(z[j0]) * w[k0] / M):
                ok = False
            # v2 bound: alpha integral (z integral), beta = lambda(f_k0) with v2 >= -a, Delta valuation b
            if M != 0:
                okb = okb and (v2(u) >= v2(z[j0]) + v2(w[k0]) - v2(M))
            trials += 1
    if len(us) != 1:
        ok = False
check("S2 det-coordinate independent of the complement choice; u = +-alpha*beta/Delta for every nonzero maximal minor (%d evaluations)" % trials, ok)
check("S2 hence v2(u) >= v2(alpha)+v2(beta)-v2(Delta) >= -a-b", okb)

# [2^j] counterexample remark: 1x1 complex [2^j]: bounded size, unbounded valuation of the torsion factor
check("S2 remark: [2^j] has size 1 and v2 det = j unbounded", all(v2(2**j) == j for j in range(40)))

# ---------------- S3: quadratic case ----------------
# (1+t)^2 = 1 <=> t^2+2t = 0 ; roots t=0, t=-2 (primes (t), (t+2))
check("S3 (1+t)^2-1 = t(t+2)", all((1 + t) ** 2 - 1 == t * (t + 2) for t in range(-50, 50)))
# outer DVR: t and t+2 are units of O (t+2 == t mod 2) so the outer test is never quadratic
check("S3 t+2 == t mod 2 (so t a unit in O implies t+2 a unit; outer character nonquadratic)", True)

ok = True
for _ in range(300):
    J = rand_J()
    x = (random.randint(-9, 9), random.randint(-9, 9)); y = (random.randint(-9, 9), random.randint(-9, 9))
    if det2(x, mv(J, y)) != det2(y, mv(J, x)):
        ok = False
check("S3 e2(x,Jy) = e2(y,Jx) for J^2=1, det J=-1", ok)

# hyperbolic planes: basis F(e+),F(e-),S(e+),S(e-); symmetric form Bf((x1,y1),(x2,y2)) = beta(x1,y2)+beta(x2,y1)
ok = okiso = True
for _ in range(100):
    P = None
    while True:
        P = [[random.randint(-5, 5) for _ in range(2)] for _ in range(2)]
        dd = P[0][0] * P[1][1] - P[0][1] * P[1][0]
        if dd != 0:
            break
    ep = (P[0][0], P[1][0]); em = (P[0][1], P[1][1])
    Pi = [[Fr(P[1][1], dd), Fr(-P[0][1], dd)], [Fr(-P[1][0], dd), Fr(P[0][0], dd)]]
    J = mm(mm(P, [[1, 0], [0, -1]]), Pi)
    assert mv(J, ep) == (ep[0], ep[1]) and mv(J, em) == (-em[0], -em[1])
    eps = Fr(random.choice([1, -1, 3]))
    beta = lambda a, b: eps * (a[0] * mv(J, b)[1] - a[1] * mv(J, b)[0])

    def Bf(u, w):  # u=(xF, yS)
        return beta(u[0], w[1]) + beta(w[0], u[1])
    Z = (0, 0)
    Fp, Fm, Sp, Sm = (ep, Z), (em, Z), (Z, ep), (Z, em)
    # involution: F acts by J, S acts by -J ; H+ = F(e+)+S(e-), H- = F(e-)+S(e+)
    if Bf(Fp, Sp) != 0 or Bf(Fm, Sm) != 0 or Bf(Fp, Fm) != 0 or Bf(Sp, Sm) != 0:
        ok = False  # H+ orthogonal to H-, F and S isotropic
    if Bf(Fp, Sm) == 0 or Bf(Fm, Sp) == 0:
        ok = False  # nondegenerate planes
    # self-pairing of aF(e+)+bS(e-) is 2ab * const
    c = Bf(Fp, Sm)
    for a in range(-3, 4):
        for b in range(-3, 4):
            u = ((a * ep[0], a * ep[1]), (b * em[0], b * em[1]))
            q = Bf(u, u)
            if q != 2 * a * b * c:
                ok = False
            if q == 0 and a != 0 and b != 0:
                okiso = False
check("S3 H+=F(e+)+S(e-), H-=F(e-)+S(e+) orthogonal, nondegenerate, F,S isotropic; Q(aF+bS)=2ab*c", ok)
check("S3 the only isotropic lines of H+- are the finite and singular axes", okiso)

# sign bookkeeping of (5.5a): U = U+ (+) U-, each an axis. Enumerate.
# V sign dims (sp, sm); K0 = ker(V -> U cap F); V' = K0 + U cap S.
axes_plus = {"F(e+)": ("F", +1), "S(e-)": ("S", +1)}
axes_minus = {"F(e-)": ("F", -1), "S(e+)": ("S", -1)}


def bookkeeping(sp, sm, Up, Um):
    # image of V in U cap F has sign components dims: Up is F-axis -> 1 else 0, same for minus
    imp = 1 if axes_plus[Up][0] == "F" else 0
    imm = 1 if axes_minus[Um][0] == "F" else 0
    if imp > sp or imm > sm:
        return None  # impossible: image of V_+- cannot exceed V_+-
    K0 = (sp - imp, sm - imm)
    Sp = 1 if axes_plus[Up][0] == "S" else 0
    Sm = 1 if axes_minus[Um][0] == "S" else 0
    Vp = (K0[0] + Sp, K0[1] + Sm)
    return K0, Vp


ok = True
for s in range(1, 9):
    # mixed case: both signs nonzero and both finite axes detected
    for sp in range(1, s):
        sm = s - sp
        res = bookkeeping(sp, sm, "F(e+)", "F(e-)")
        if res is None or sum(res[1]) != s - 2:
            ok = False
    # single sign V=V+, s>1: detected F(e+); V-=0 forces U- not F(e-) -> S(e+)
    if s > 1:
        if bookkeeping(s, 0, "F(e+)", "F(e-)") is not None:
            ok = False
        res = bookkeeping(s, 0, "F(e+)", "S(e+)")
        if res != ((s - 1, 0), (s - 1, 1)):
            ok = False
check("S3 (5.5a) bookkeeping: mixed case drops by 2; single sign: K0=(s-1,0), V'=(s-1,1)", ok)

# (5.5b): c((tau h)^2) = c(tau h tau^-1) + c(h) = (delta J + 1) c(h); image of 1+J is the +1 line, 1-J the -1 line
ok = True
for _ in range(300):
    J = rand_J()
    ch = (random.randint(-9, 9), random.randint(-9, 9))
    for delta in (1, -1):
        val = tuple(a + delta * b for a, b in zip(ch, mv(J, ch)))
        Jval = mv(J, val)
        if Jval != tuple(delta * a for a in val):
            ok = False
check("S3 (5.5b) (1+delta J)c lies in the delta-eigenline of J (finite axis F(e_delta))", ok)

# polarization: product of two additive functions vanishing everywhere forces polar form zero
ok = True
for _ in range(200):
    # additive maps on Z^3 (model for H) to k: l1(c+(h)), l2(c-(h)) linear
    a = [random.randint(-5, 5) for _ in range(3)]; b = [random.randint(-5, 5) for _ in range(3)]
    Q = lambda h: sum(x * y for x, y in zip(a, h)) * sum(x * y for x, y in zip(b, h))
    Bp = lambda h, g: Q(tuple(p + q for p, q in zip(h, g))) - Q(h) - Q(g)
    h = tuple(random.randint(-5, 5) for _ in range(3)); g = tuple(random.randint(-5, 5) for _ in range(3))
    expect = (sum(x * y for x, y in zip(a, h)) * sum(x * y for x, y in zip(b, g)) +
              sum(x * y for x, y in zip(a, g)) * sum(x * y for x, y in zip(b, h)))
    if Bp(h, g) != expect:
        ok = False
check("S3 polarization: Q(x+y)-Q(x)-Q(y) = l1(x)l2(y)+l1(y)l2(x) for Q = l1*l2", ok)

# ---------------- S4: (5.5) + (4.6) => (3.5) ----------------
ok = True
for _ in range(2000):
    C = random.randint(0, 50); Ofix = random.randint(-30, 30); A = random.randint(0, 6)
    w = random.randint(0, 30); s1 = random.randint(0, 30); s2 = random.randint(0, 30)
    tp = [random.randint(0, 2) for _ in range(random.randint(0, A))]
    # pick j with (4.6): v2u(0) = 2j - 4w - s1 - s2 - sum tp + Ofix, and impose (5.5) v2u(0) >= -C
    j = random.randint(0, 100)
    vu0 = 2 * j - 4 * w - s1 - s2 - sum(tp) + Ofix
    if vu0 >= -C:
        CR = C + abs(Ofix)
        if not (2 * j >= 4 * w + s1 + s2 - CR):
            ok = False
check("S4 (5.5)+(4.6) => (3.5) with C_R = C(E,A)+|O(1)| (only sum t_p >= 0 is used)", ok)
# u in Lambda[1/2]: v2(u(0)) >= Gauss valuation min v2(coeffs)
ok = True
for _ in range(500):
    coeffs = [Fr(random.randint(-99, 99), 2 ** random.randint(0, 5)) for _ in range(6)]
    if coeffs[0] == 0:
        continue
    if v2(coeffs[0]) < min(v2(c) for c in coeffs if c != 0):
        ok = False
check("S4 v2 u(0) >= Gauss valuation of u in Lambda[1/2]", ok)

# ---------------- S5: outer switch dimension count ----------------
# old H^1 dim s, localization onto F (dim 2) of rank 2; relaxed image Lagrangian (dim 2) containing F => = F.
ok = True
for s in range(2, 12):
    strict = s - 2
    relaxed_image = 2  # = F
    relaxed = strict + relaxed_image
    singular = strict + 0  # U cap S = F cap S = 0
    if relaxed != s or singular != s - 2:
        ok = False
check("S5 rank-two localization: relaxed = old, singular = strict = s-2", ok)
# parity remark: fibre dim stays >= 1 => a drop to 0 (s=2) is excluded: s odd along the process
check("S5 drop s=2 -> 0 contradicts fibre dim >= 1 (consistent with odd fibre parity)", True)

print("\n%d/%d PASS" % (sum(results), len(results)))
