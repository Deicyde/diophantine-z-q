"""tyz-35: pure-Python (double precision; no PARI on this host) test of the leaf TYZThm33Pinned at n = 7 (mod 8),
the part of TYZ Theorem 3.3 that tyz-t1 did not test numerically.

Model (tyz-t1 heeg.py, re-implemented): A = X0(32) = 32a1 : y^2 = x^3 + 4x, phi(tau) = sum a_n/n q^n in C/Lambda.
n = 7: z_n^c = phi(tau_Q) over Heegner forms [A,B,C], 32 | A, B = delta mod 64, disc -n (one per class);
       P_T(n) = sum_c chi_T(c) z_n^c, chi_T(c) = Jacobi(m_c / g), g = gmap(n, d1) (Lean `pairSet`).
d0 = 5: P_1(d0) = (S_1 - i S_{d0}) / 4, S over Heegner forms of disc -64 d0, B = -8 mod 64 (tyz-t1 sec. 3.1).
d0 = 7: P_1(d0) = sum of z_{d0}^c.
Check (TYZ Thm 3.3 with the leaf's chi_{d0,d1}): for d1 = 1, 3 (mod 8), 16 P_T(n) = M eps P_1(d0) mod Lambda,
M = +-16 2^(h2(n)-h2(d0)) L(d1), eps = 1 (d0 = 7), i (d0 = 5); if P_1(d0) torsion or L(d1) = 0: P_T(n) torsion.
Usage: python3 heeg7.py n1 n2 ... (sequential)."""
import sys, math, cmath

NMAX = 6000


def legendre(a, p):
    a %= p
    if a == 0: return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def primes_upto(N):
    s = bytearray([1]) * (N + 1); s[0] = s[1] = 0
    for i in range(2, int(N ** 0.5) + 1):
        if s[i]: s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(N + 1) if s[i]]


PR = primes_upto(NMAX)


def ap_curve(p, a4):  # y^2 = x^3 + a4 x, p odd
    return -sum(legendre(x * x * x + a4 * x, p) for x in range(p))


def an_table(apf, N):
    a = [0] * (N + 1); a[1] = 1
    for p in PR:
        if p > N: break
        ap = apf(p)
        pk, prev2, prev = p, 1, ap
        a_pk = {1: 1, p: ap}
        k = p
        while k * p <= N:
            nxt = ap * a_pk[k] - (p * a_pk[k // p] if ap is not None and p != 2 else 0)
            if p == 2: nxt = 0
            a_pk[k * p] = nxt; k *= p
        # multiplicative fill
        for m in range(N // p, 0, -1):
            if a[m] == 0 or m % p == 0: continue
            q = p
            while m * q <= N:
                a[m * q] = a[m] * a_pk[q]; q *= p
    return a


AP32 = {}
def ap32(p):
    if p == 2: return 0
    return ap_curve(p, 4)


A32 = an_table(ap32, NMAX)


def zphi(tau):
    q = cmath.exp(2j * math.pi * tau)
    if abs(q) ** NMAX > 1e-20: raise ValueError("series not converged, Im tau = %g" % tau.imag)
    s = 0j; qq = 1
    for k in range(1, NMAX + 1):
        qq *= q
        if A32[k]: s += A32[k] / k * qq
        if abs(qq) < 1e-22: break
    return s


def tau_of(A, B, C):
    D = B * B - 4 * A * C
    return (-B + 1j * math.sqrt(-D)) / (2 * A)


# ---- period lattice from Gamma0(32) differences
def lattice():
    vecs = []
    for d in (1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23):
        # [[a, b], [32, d]] with a d - 32 b = 1
        a = pow(d, -1, 32); b = (a * d - 1) // 32
        t0 = complex(-d / 32, 1 / 32)
        gt = (a * t0 + b) / (32 * t0 + d)
        vecs.append(zphi(gt) - zphi(t0))
    vecs = [v for v in vecs if abs(v) > 1e-6]
    # 2D lattice reduction
    b1 = min(vecs, key=abs)
    b2 = None
    for v in sorted(vecs, key=abs):
        if abs((v / b1).imag) > 1e-3: b2 = v; break
    for _ in range(50):
        changed = False
        for v in vecs:
            x = reduce(v, b1, b2)
            if abs(x) > 1e-7:  # v not in lattice spanned: refine basis
                if abs(x) < abs(b2): b2 = x; changed = True
        if abs(b2) < abs(b1): b1, b2 = b2, b1; changed = True
        mu = round((b2 / b1).real)
        if mu: b2 -= mu * b1; changed = True
        if not changed: break
    return b1, b2


def coords(z, b1, b2):
    det = (b1.conjugate() * b2).imag
    x = (z.conjugate() * b2).imag / det   # z = x b1 + y b2
    y = (b1.conjugate() * z).imag / det
    return x, y


def reduce(z, b1, b2):
    x, y = coords(z, b1, b2)
    return (x - round(x)) * b1 + (y - round(y)) * b2


def in_lattice(z, tol=1e-6):
    x, y = coords(z, B1, B2)
    return abs(x - round(x)) < tol and abs(y - round(y)) < tol


# ---- binary quadratic forms
def qfbred(a, b, c):
    while True:
        if c < a or (c == a and b < 0): a, b, c = c, -b, a; continue
        if b > a or b <= -a:
            k = (a - b) // (2 * a)
            c = a * k * k + b * k + c; b = b + 2 * a * k; continue
        return (a, b, c)


def classno(D):
    h = 0; a = 1
    while 3 * a * a <= -D:
        for b in range(-a + 1, a + 1):
            if (b * b - D) % (4 * a) == 0:
                c = (b * b - D) // (4 * a)
                if c >= a and math.gcd(math.gcd(a, b), c) == 1 and not (b < 0 and a == c): h += 1
        a += 1
    return h


def heegner_forms(D, beta):
    h = classno(D); reps = {}
    for a in range(1, 4000):
        A = 32 * a
        for j in range(a):
            B = beta + 64 * j
            if (B * B - D) % (4 * A): continue
            C = (B * B - D) // (4 * A)
            if math.gcd(math.gcd(A, B), C) != 1: continue
            key = qfbred(A, B, C)
            if key not in reps: reps[key] = (A, B, C)
        if len(reps) == h: return reps
    raise RuntimeError("classes not all hit")


def jacobi(a, n):
    a %= n; r = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5): r = -r
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3: r = -r
        a %= n
    return r if n == 1 else 0


def rep_value(Q, n):
    A, B, C = Q
    for s in range(1, 80):
        for x in range(-s, s + 1):
            for y in (s - abs(x), -(s - abs(x))):
                m = A * x * x + B * x * y + C * y * y
                if m > 0 and m % 2 == 1 and math.gcd(m, n) == 1: return m
    raise ValueError


def coredisc(d):
    return d if d % 4 == 1 else 4 * d


def kron(D, m):
    return jacobi(D % m, m) if m > 1 else 1


def delta7(n):
    for d in range(1, 128, 2):
        if (d * d + n) % 128 == 0: return d


def factor_odd(n):
    return [p for p in PR if p > 2 and n % p == 0]


def h2(d):
    k = len(factor_odd(d)); return k if d % 8 == 5 else k - 1


def gmap(n, d1):
    return d1 if d1 % 4 == 1 else n // d1


A1 = an_table(lambda p: 0 if p == 2 else ap_curve(p, -1), NMAX)
OM1 = None


def omega1():  # real period of y^2 = x^3 - x: 2 * int_1^oo dx/sqrt(x^3-x) = 2*Gamma(1/4)^2/(2 sqrt(2 pi))
    return 2 * math.gamma(0.25) ** 2 / (2 * math.sqrt(2 * math.pi))


def Lcal(d):
    """|L(d)| with L(d)^2 = L(E_d,1)/(2^(2k-3) Omega_1/sqrt d), d odd squarefree, d = 1,3 mod 8 (root number +1)."""
    if d == 1: return 1
    N = 32 * d * d; sN = math.sqrt(N)
    s = 0.0
    for k in range(1, NMAX + 1):
        if A1[k] == 0 or math.gcd(k, 2 * d) != 1: continue
        t = math.exp(-2 * math.pi * k / sN)
        if t < 1e-18: break
        chi = jacobi(d, k) if True else 1   # twist by Q(sqrt d): chi(p) = (d/p) for odd p not dividing d
        s += chi * A1[k] / k * t
    L = 2 * s
    kk = len(factor_odd(d))
    val = L / (2 ** (2 * kk - 3) * omega1() / math.sqrt(d))
    r = round(math.sqrt(abs(val))) if val > 1e-8 else 0
    assert abs(val - r * r) < 1e-4, (d, val)
    return r


def P_T_seven(n, gs):
    reps = heegner_forms(-n, delta7(n))
    out = {g: 0j for g in gs}
    for Q in reps.values():
        z = zphi(tau_of(*Q)); m = rep_value(Q, n)
        for g in gs: out[g] += (jacobi(m, g) if g > 1 else 1) * z
    return out


def P1_five(d0):
    reps = heegner_forms(-64 * d0, -8)
    s1 = 0j; sd = 0j
    for Q in reps.values():
        z = zphi(tau_of(*Q)); m = rep_value(Q, d0)
        s1 += z; sd += kron(coredisc(d0), m) * z
    return (s1 - 1j * sd) / 4


def run7(n):
    divs = [d for d in range(1, n + 1) if n % d == 0]
    P = P_T_seven(n, sorted(set(divs)))
    bad = 0
    for d1 in divs:
        d0 = n // d1; g = gmap(n, d1)
        if d1 % 8 in (5, 7):
            ok = in_lattice(P[g] - P[n // g])
            print("  n=%d d1=%d noncontrib: chi_T = chi_{T^c} on P: %s" % (n, d1, ok)); bad += not ok
            continue
        Ld = Lcal(d1)
        p0 = P1_five(d0) if d0 % 8 == 5 else P_T_seven(d0, [1])[1]
        eps = 1j if d0 % 8 == 5 else 1
        z16 = 16 * P[g]
        p0tor = in_lattice(16 * p0)
        if p0tor or Ld == 0:
            ok = in_lattice(z16)
            print("  n=%d (d0,d1)=(%d,%d) L(d1)=%d P1(d0) torsion=%s: P_T torsion: %s" % (n, d0, d1, Ld, p0tor, ok))
            bad += not ok; continue
        pred = 16 * 2 ** (h2(n) - h2(d0)) * Ld
        hits = [M for M in range(-4 * pred - 64, 4 * pred + 65) if in_lattice(z16 - M * eps * p0)]
        ok = hits in ([pred], [-pred])
        print("  n=%d (d0,d1)=(%d,%d) L(d1)=%d eps=%s: 16 P_T = M eps P1(d0) for M in %s, predicted +-%d: %s"
              % (n, d0, d1, Ld, 'i' if eps == 1j else '1', hits, pred, ok))
        bad += not ok
    print("n=%d: mismatches %d" % (n, bad)); sys.stdout.flush()
    return bad


B1, B2 = lattice()
if __name__ == "__main__":
    print("lattice basis:", B1, B2, "ratio", B2 / B1); sys.stdout.flush()
    tot = 0
    for a in sys.argv[1:]:
        tot += run7(int(a))
    print("total mismatches:", tot)
