"""mcheck-appF s3: a global toy model of (O.4), (O.6) and (O.7).

Model: B = (-1,-3), ramified exactly at ell_0 = 3 and infinity; R = Z<1, i, (1+j)/2, (i+k)/2>
maximal, class number one, |R^x| = 12. Level N = 1, so there are no root characters and
omega(N) = 0. Take h_* = -m with m in {7, 31} (negative odd fundamental discriminants, split at 2,
(h_*/3) = -1, no extra units). The function P is the constant 1, which is the Brandt eigenvector of
eigenvalue p+1 (Eisenstein), with uniformizer eigenvalue +1. The local weights are exactly those of
tex L8474-8566:
  * at 3: x mod (j) = t*beta in F_9 with beta = i, weight (t/3), zero if t = 0;
  * at p | m: v_p Nrd(x) = 1 and the nilpotent sign eps_p(g X0 g^-1) = (det g / p);
  * at 2: variant B (tex): (1+x)/2 in R and x^2 in Z_2^{x2}; variant A: 1_{R_2^0} (for the recurrence only);
  * elsewhere 1_{R_p^0}.
With c0 = |R^x| = 12 and one class, H(n) = sum_{x in R^0, Nrd x = n} f(x).

Predictions from the tex:
  (O.6) analogue (L9078-9081, with a_p -> p+1):
     H(p^2 n) + s(-n/p) H(n) + p s^2 H(n/p^2) = s chi_{h*}(p) (p+1) H(n),  s = prod_{v != p} alpha_v(p) = (p/3)(p/m)
  (O.7) analogue (L9101-9117 and its proof): for admissible D (D = 1 mod 24, squarefree, prime to m),
     H(mD) = c0 2^0 zeta sum_{[a] in Pic O_F} chi_F(a) P(z_a) = 12 zeta h(F) [D = 1] , 0 [D > 1];
     and the unweighted count of embeddings is (|R^x|/2) * h(F) * 2^{omega(N)+1} = 12 h(F).
"""
import math

results = []


def check(name, ok, info=""):
    results.append((name, bool(ok)))
    print(("PASS " if ok else "FAIL ") + name + ((" : " + str(info)) if info else ""))


def neg(name, claim_value, info=""):
    check("NEG " + name + " (wrong input must fail)", not claim_value, info)


def leg(a, p):
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def kron(D, n):
    r = 1
    while n % 2 == 0:
        n //= 2
        if D % 2 == 0:
            return 0
        r *= 1 if D % 8 in (1, 7) else -1
    q = 3
    nn = n
    # factor n (small)
    f = 2
    res = r
    x = nn
    p = 3
    while x > 1:
        if x % p == 0:
            while x % p == 0:
                res *= leg(D, p)
                x //= p
        p += 2
        if p * p > x and x > 1:
            res *= leg(D, x)
            break
    return res


def class_number(d):
    """h(d) for a negative discriminant d: count reduced forms."""
    h = 0
    a = 1
    while 3 * a * a <= -d:
        for b in range(-a + 1, a + 1):
            if (b * b - d) % (4 * a):
                continue
            c = (b * b - d) // (4 * a)
            if c < a:
                continue
            if c == a and b < 0:
                continue
            if math.gcd(math.gcd(a, abs(b)), c) != 1:
                continue
            h += 1
        a += 1
    return h


NMAX = 26000


def enumerate_R0(nmax):
    """Trace-zero x = alpha i + beta j + gamma k in R; stored as (u, a, d): alpha = u/2, beta = -a, gamma = d/2,
    u = d mod 2, 4 Nrd = u^2 + 12 a^2 + 3 d^2."""
    out = []
    A = int(math.isqrt(nmax // 3)) + 1
    Dm = int(math.isqrt(4 * nmax // 3)) + 1
    for a in range(-A, A + 1):
        for d in range(-Dm, Dm + 1):
            rest = 4 * nmax - 12 * a * a - 3 * d * d
            if rest < 0:
                continue
            U = int(math.isqrt(rest))
            for u in range(-U, U + 1):
                if (u - d) % 2:
                    continue
                n4 = u * u + 12 * a * a + 3 * d * d
                if n4 == 0:
                    continue
                out.append((u, a, d, n4 // 4))
    return out


def find_IJ(p):
    I = ((0, -1), (1, 0))
    for c in range(p):
        for e in range(p):
            if (c * c + e * e + 3) % p == 0:
                return I, ((c, e), (e, -c))
    raise ValueError


def mat_add(*Ms):
    return tuple(tuple(sum(M[i][j] for M in Ms) for j in range(2)) for i in range(2))


def mat_scale(c, M, p):
    return tuple(tuple(c * M[i][j] % p for j in range(2)) for i in range(2))


def mat_mul(A, B, p):
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(2)) % p for j in range(2)) for i in range(2))


def eps_nil(N, p):
    """(det g / p) with g^-1 N g = X0, for a nonzero nilpotent N mod p."""
    for v in ((1, 0), (0, 1)):
        Nv = ((N[0][0] * v[0] + N[0][1] * v[1]) % p, (N[1][0] * v[0] + N[1][1] * v[1]) % p)
        if Nv != (0, 0):
            return leg(Nv[0] * v[1] - Nv[1] * v[0], p)
    raise ValueError


def make_weight(m, variant):
    mp = [q for q in range(3, m + 1) if m % q == 0 and all(q % r for r in range(2, q))]
    IJs = {q: find_IJ(q) for q in mp}

    def f(x):
        u, a, d, n = x
        # at 3: t = alpha mod 3, alpha = u/2
        t = (u * 2) % 3  # 1/2 = 2 mod 3
        if t == 0:
            return 0
        w = leg(t, 3)
        for q in mp:
            if n % q or (n // q) % q == 0:
                return 0
            I, J = IJs[q]
            inv2 = pow(2, -1, q)
            al, be, ga = u * inv2 % q, (-a) % q, d * inv2 % q
            IJ = mat_mul(I, J, q)
            N = mat_add(mat_scale(al, I, q), mat_scale(be, J, q), mat_scale(ga, IJ, q))
            N = tuple(tuple(z % q for z in row) for row in N)
            w *= eps_nil(N, q)
        if variant == "B":
            # (1+x)/2 in R: beta odd, d even, (u-d)/2 even ; x^2 = -n in Z_2^{x2}: n = 7 mod 8
            if not (a % 2 == 1 and d % 2 == 0 and ((u - d) // 2) % 2 == 0):
                return 0
            if n % 8 != 7:
                return 0
        return w

    return f


elts = enumerate_R0(NMAX)
check("toy enumeration sanity: #{x in R^0 : Nrd x = 1} = 6 (units i-type: +-i, +-(i+-k)/2 ...)",
      sum(1 for x in elts if x[3] == 1) == 2 + 4, sum(1 for x in elts if x[3] == 1))

for m in (7, 31):
    hstar = -m
    # sanity on h_*: split at 2, inert at 3
    assert hstar % 8 == 1 and kron(hstar, 3) == -1
    for variant in ("A", "B"):
        f = make_weight(m, variant)
        H = {}
        for x in elts:
            w = f(x)
            if w:
                H[x[3]] = H.get(x[3], 0) + w
        Hg = lambda n: H.get(n, 0) if (n == int(n) and n > 0) else 0
        # f(-x) = f(x) (alpha(-1) = (-1/3)(-1/m) = 1), and theta not identically zero
        nonzero = sum(1 for v in H.values() if v)
        check("m=%d variant %s: weighted theta nonzero (%d nonzero coefficients <= %d)" % (m, variant, nonzero, NMAX), nonzero > 0)
        ok = True
        okneg_s = True
        okneg_leg = True
        tested = 0
        for p in (5, 11, 13, 17, 19, 23):
            if m % p == 0:
                continue
            s = leg(p, 3) * leg(p, m)
            chi = kron(hstar, p)
            for n in range(1, NMAX // (p * p) + 1):
                lhs = Hg(p * p * n) + s * kron(-n, p) * Hg(n) + p * s * s * (Hg(n // (p * p)) if n % (p * p) == 0 else 0)
                rhs = s * chi * (p + 1) * Hg(n)
                ok &= lhs == rhs
                tested += 1
                l1 = Hg(p * p * n) + 1 * kron(-n, p) * Hg(n) + p * (Hg(n // (p * p)) if n % (p * p) == 0 else 0)
                if l1 != chi * (p + 1) * Hg(n):
                    okneg_s = False
                l2 = Hg(p * p * n) + s * kron(n, p) * Hg(n) + p * (Hg(n // (p * p)) if n % (p * p) == 0 else 0)
                if l2 != rhs:
                    okneg_leg = False
        check("m=%d variant %s: (O.6)-analogue H(p^2n)+s(-n/p)H(n)+ps^2H(n/p^2) = s chi(p)(p+1)H(n), %d (p,n) pairs" % (m, variant, tested), ok)
        neg("m=%d variant %s: same recurrence with s := 1" % (m, variant), okneg_s)
        neg("m=%d variant %s: same recurrence with (n/p) for (-n/p)" % (m, variant), okneg_leg)

    # (O.7) analogue, variant B (the tex's dyadic support)
    f = make_weight(m, "B")
    ok_count = True
    ok_sum = True
    ok_split = True
    okneg_noch = True
    nD = 0
    report = []
    for D in range(1, NMAX // m + 1, 24):
        if math.gcd(D, m) > 1 or any(D % (q * q) == 0 for q in range(2, int(math.isqrt(D)) + 1)):
            continue
        n = m * D
        if n > NMAX:
            break
        X = [x for x in elts if x[3] == n]
        W = [f(x) for x in X]
        emb = [w for w in W if w != 0]  # support = optimal embeddings O_F -> R with the local conditions
        hF = class_number(-m * D)
        S = sum(W)
        ok_count &= len(emb) == 12 * hF  # (|R^x|/2) * h(F) * 2^{omega(N)+1}
        if D == 1:
            ok_sum &= abs(S) == 12 * hF and len(set(emb)) == 1  # all orientations contribute equally
        else:
            ok_sum &= S == 0
            ok_split &= emb.count(1) == emb.count(-1)
        if S != 12 * hF:
            okneg_noch = okneg_noch and False
        nD += 1
        report.append((D, hF, len(emb), S))
    check("m=%d (O.7)-analogue: #support embeddings of norm mD = (|R^x|/2) h(F) 2^{omega(N)+1} = 12 h(F), %d values of D" % (m, nD), ok_count, report[:6])
    check("m=%d (O.7)-analogue: H(m) = +-12 h(F) with all weights equal (D=1); H(mD) = 0 = 12 zeta sum chi_F (D>1)" % m, ok_sum)
    check("m=%d (O.7)-analogue: D>1 weights split evenly (genus character pattern)" % m, ok_split)
    neg("m=%d H(mD) = 12 h(F) for all D (genus character dropped)" % m, okneg_noch)
    neg("m=%d count = 6 h(F) (one orientation at ell_0 only)" % m, all(r[2] == 6 * r[1] for r in report))

npass = sum(ok for _, ok in results)
print("\n%d/%d PASS" % (npass, len(results)))
