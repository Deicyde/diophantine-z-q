"""Fourier coefficients: Igusa's theta expressions (theta-glue's Lean definitions, parsed from the Lean text)
against the Siegel Eisenstein series psi_k of degree 2 (Maass/Cohen coefficient formula) and Igusa's 1962
cusp forms chi10, chi12 (constants as recalled, UNVERIFIED; this script checks them).

Usage: python -I fourier.py ThetaGlue.lean
Exact arithmetic throughout (Gaussian integers as pairs, Fractions).

Conventions. Omega = [[t1, z], [z, t2]].  e(T, Omega) = exp(2 pi i (n t1 + r z + m t2)) for
T = (n, r, m) <-> [[n, r/2], [r/2, m]].  theta_m(Omega) = sum_x exp(pi i x^T Omega x + pi i x.b), x = n + a/2.
Exponent bookkeeping: E1 = 8 * (x0^2/2), Ez = 8 * x0 x1, E2 = 8 * (x1^2/2), so T = (E1/8, Ez/8, E2/8).
"""
import sys, re, itertools
from fractions import Fraction as F
from math import gcd

MAXN = int(sys.argv[2]) if len(sys.argv) > 2 else 1
MAXE = 8 * MAXN  # keep E1, E2 <= 8 MAXN, i.e. n, m <= MAXN

# ---------- Gaussian-integer power series in (E1, Ez, E2) ----------
def gmul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])

def smul(A, B):
    C = {}
    for (a1, az, a2), ca in A.items():
        for (b1, bz, b2), cb in B.items():
            e1 = a1 + b1; e2 = a2 + b2
            if e1 > MAXE or e2 > MAXE:
                continue
            k = (e1, az + bz, e2)
            p = gmul(ca, cb)
            if k in C:
                q = C[k]; C[k] = (q[0] + p[0], q[1] + p[1])
            else:
                C[k] = p
    return {k: v for k, v in C.items() if v != (0, 0)}

def sadd(A, B, s=1):
    C = dict(A)
    for k, v in B.items():
        q = C.get(k, (0, 0)); C[k] = (q[0] + s * v[0], q[1] + s * v[1])
    return {k: v for k, v in C.items() if v != (0, 0)}

def theta(a, b):
    S = {}
    R = 2 * MAXN + 2
    for n0 in range(-R, R + 1):
        for n1 in range(-R, R + 1):
            x0 = F(2 * n0 + a[0], 2); x1 = F(2 * n1 + a[1], 2)
            e1 = 4 * x0 * x0; ez = 8 * x0 * x1; e2 = 4 * x1 * x1
            if e1 > MAXE or e2 > MAXE:
                continue
            # phase exp(pi i (x0 b0 + x1 b1)) = i^(2 (x0 b0 + x1 b1))
            ph = int(2 * (x0 * b[0] + x1 * b[1])) % 4
            c = [(1, 0), (0, 1), (-1, 0), (0, -1)][ph]
            k = (int(e1), int(ez), int(e2))
            q = S.get(k, (0, 0)); S[k] = (q[0] + c[0], q[1] + c[1])
    return {k: v for k, v in S.items() if v != (0, 0)}

def spow(A, n):
    R = {(0, 0, 0): (1, 0)}
    for _ in range(n):
        R = smul(R, A)
    return R

# ---------- parse the Lean definitions ----------
def parse(text, name):
    i = text.index('def ' + name)
    j = text.index('\n\n', i)
    body = text[i:j]
    terms = []
    for line in body.split('\n'):
        mm = re.findall(r"t \(!\[(\d), (\d)\], !\[(\d), (\d)\]\)", line)
        if not mm:
            continue
        s = line.strip()
        sign = -1 if s.startswith('-') else 1
        chars = [((int(a), int(b)), (int(c), int(d))) for a, b, c, d in mm]
        terms.append((sign, chars))
    return terms

def coeffs(S, keys):
    out = {}
    for (n, r, m) in keys:
        v = S.get((8 * n, 8 * r, 8 * m), (0, 0))
        out[(n, r, m)] = v
    return out

# ---------- Eisenstein side ----------
from sympy import bernoulli, Rational, factorint, divisors, mobius
from sympy import Symbol
from sympy.ntheory import jacobi_symbol

def kron(D, n):
    # Kronecker symbol (D/n), n > 0
    if n == 1:
        return 1
    res = 1
    f = factorint(n)
    for p, e in f.items():
        if p == 2:
            if D % 2 == 0:
                v = 0
            elif D % 8 in (1, 7):
                v = 1
            else:
                v = -1
        else:
            v = jacobi_symbol(D % p, p) if D % p else 0
        res *= v ** e
    return res

def fund(N):
    # -N = D0 f^2 with D0 fundamental
    D = -N
    best = None
    for f in range(1, int(N ** 0.5) + 2):
        if D % (f * f) == 0:
            D0 = D // (f * f)
            if D0 % 4 == 1 or (D0 % 4 == 0 and (D0 // 4) % 4 in (2, 3)):
                best = (D0, f)
    return best

def genbern(r, D0):
    fD = abs(D0)
    x = Symbol('x')
    s = Rational(0)
    for a in range(1, fD + 1):
        s += kron(D0, a) * bernoulli(r, Rational(a, fD))
    return fD ** (r - 1) * s

def Lneg(r, D0):  # L(1-r, chi_D0) = -B_{r,chi}/r
    return -genbern(r, D0) / r

def sigma(k, n):
    return sum(d ** k for d in divisors(n))

def H(r, N):
    if N == 0:
        from sympy import zeta
        return zeta(1 - 2 * r)
    D0, f = fund(N)
    s = 0
    for d in divisors(f):
        s += mobius(d) * kron(D0, d) * d ** (r - 1) * sigma(2 * r - 1, f // d)
    return Lneg(r, D0) * s

def zneg(k):  # zeta(1-k) = -B_k/k
    return -bernoulli(k) / k

def eis(k, T):
    n, r, m = T
    if n == 0 and r == 0 and m == 0:
        return Rational(1)
    disc = 4 * n * m - r * r
    assert disc >= 0
    if disc == 0:
        t = gcd(gcd(n, m), abs(r))
        return Rational(-2 * k) / bernoulli(k) * sigma(k - 1, t)
    c = 2 / (zneg(k) * zneg(2 * k - 2))
    e = gcd(gcd(n, m), abs(r))
    return c * sum(Rational(d) ** (k - 1) * H(k - 1, disc // (d * d)) for d in divisors(e))

def semidef(maxn):
    out = []
    for n in range(maxn + 1):
        for m in range(maxn + 1):
            for r in range(-2 * maxn, 2 * maxn + 1):
                if r * r <= 4 * n * m:
                    out.append((n, r, m))
    return out

TS = semidef(MAXN)

def conv(a, b):
    out = {}
    for T in TS:
        s = 0
        for T1 in TS:
            T2 = (T[0] - T1[0], T[1] - T1[1], T[2] - T1[2])
            if T2 in a and T1 in b:
                s += b[T1] * a[T2]
        out[T] = s
    return out

if __name__ == '__main__':
    text = open(sys.argv[1]).read()
    chars = [((0, 0), (0, 0)), ((0, 0), (0, 1)), ((0, 0), (1, 0)), ((0, 0), (1, 1)),
             ((0, 1), (0, 0)), ((0, 1), (1, 0)), ((1, 0), (0, 0)), ((1, 0), (0, 1)),
             ((1, 1), (0, 0)), ((1, 1), (1, 1))]
    th = {m: theta(m[0], m[1]) for m in chars}
    t = {m: smul(th[m], th[m]) for m in chars}          # theta^2
    t4 = {m: smul(t[m], t[m]) for m in chars}           # theta^4
    # psi4 = (1/4) sum theta^8
    S8 = {}
    for m in chars:
        S8 = sadd(S8, smul(t4[m], t4[m]))
    P6 = parse(text, 'psi6T')
    P12 = parse(text, 'chi12T')
    assert len(P6) == 60 and len(P12) == 15, (len(P6), len(P12))
    S6 = {}
    for sgn, cs in P6:     # (t t t)^2 = theta^4 theta^4 theta^4
        S6 = sadd(S6, smul(smul(t4[cs[0]], t4[cs[1]]), t4[cs[2]]), sgn)
    S12 = {}
    for sgn, cs in P12:
        pr = {(0, 0, 0): (1, 0)}
        for c in cs:
            pr = smul(pr, t4[c])
        S12 = sadd(S12, pr, sgn)
    PR = {(0, 0, 0): (1, 0)}
    for m in chars:
        PR = smul(PR, t[m])
    def real(S, den):
        out = {}
        for T in TS:
            v = S.get((8 * T[0], 8 * T[1], 8 * T[2]), (0, 0))
            assert v[1] == 0, (T, v)
            out[T] = Rational(v[0], den)
        return out
    th4 = real(S8, 4)
    th6 = real(S6, 4)
    th10 = {T: -v for T, v in real(PR, 2 ** 14).items()}
    th12 = real(S12, 2 ** 17 * 3)
    # also check that no fractional exponents survive in the range (modular forms have integral T)
    for name, S in (('S8', S8), ('S6', S6), ('PR', PR), ('S12', S12)):
        bad = [k for k in S if any(e % 8 for e in k)]
        print(name, 'non-integral exponents present:', len(bad))
    E = {k: {T: eis(k, T) for T in TS} for k in (4, 6, 10, 12)}
    c10 = Rational(-43867, 2 ** 12 * 3 ** 5 * 5 ** 2 * 7 * 53)
    c12 = Rational(131 * 593, 2 ** 13 * 3 ** 7 * 5 ** 3 * 7 ** 2 * 337)
    p46 = conv(E[4], E[6])
    chi10E = {T: c10 * (p46[T] - E[10][T]) for T in TS}
    p444 = conv(conv(E[4], E[4]), E[4])
    p66 = conv(E[6], E[6])
    chi12E = {T: c12 * (3 ** 2 * 7 ** 2 * p444[T] + 2 * 5 ** 3 * p66[T] - 691 * E[12][T]) for T in TS}
    ok = True
    for name, A, B in (('psi4', th4, E[4]), ('psi6', th6, E[6]), ('chi10', th10, chi10E), ('chi12', th12, chi12E)):
        print('==', name)
        for T in TS:
            if T[1] < 0:
                continue
            flag = A[T] == B[T]
            ok &= flag
            print('  T =', T, 'theta:', A[T], ' Igusa/Eisenstein:', B[T], 'OK' if flag else 'MISMATCH')
    # Lin-Yang check of normalizations s5 = 2^12 3^5 chi10, s6 = 2^12 3^6 chi12 is in theta-glue (80 digits).
    print('ALL EQUAL' if ok else 'SOME MISMATCH')
