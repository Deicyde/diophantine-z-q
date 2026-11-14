"""tyz-321: find the Heegner form Q' with  b·(L_Q', L^N_Q') = c·(L_Q, L^N_Q)  for
b = a ∩ O4,  a = (m, -1 + w) (odd part of (w - 1), w = sqrt(-n), m = (n+1)/2),
Q = TYZ's form [16(n+1), -8, 1] (tau = (1+w)/(8m)), and identify tau_Q' = N tau_Q with N a word in
W (tau -> -1/(32 tau)) and T4 (tau -> tau + 1/4).  Exact arithmetic in K = Q(w)."""
from fractions import Fraction as Fr
from math import gcd
import itertools, sys

def mul(x, y, n):  # (a+bw)(c+dw), w^2=-n
    return (x[0]*y[0] - n*x[1]*y[1], x[0]*y[1] + x[1]*y[0])
def norm(x, n): return x[0]**2 + n*x[1]**2
def inv(x, n):
    N = norm(x, n); return (x[0]/N, -x[1]/N)
def conj(x): return (x[0], -x[1])

def hnf(vecs):
    """Z-span of rational 2-vectors -> canonical basis (upper triangular HNF)."""
    den = 1
    for v in vecs:
        for c in v: den = den*Fr(c).denominator//gcd(den, Fr(c).denominator)
    M = [[int(Fr(v[0])*den), int(Fr(v[1])*den)] for v in vecs]
    # column 1 (second coord) first
    rows = [r[:] for r in M if r != [0, 0]]
    # integer row reduction to get basis
    def red(rows, col):
        while True:
            nz = [r for r in rows if r[col] != 0]
            if len(nz) <= 1: return rows
            nz.sort(key=lambda r: abs(r[col]))
            p = nz[0]
            new = [p]
            for r in rows:
                if r is p: continue
                if r[col] != 0:
                    q = r[col]//p[col]
                    r = [r[0]-q*p[0], r[1]-q*p[1]]
                if r != [0, 0]: new.append(r)
            rows = new
    rows = red(rows, 1)
    piv = [r for r in rows if r[1] != 0]
    rest = [r for r in rows if r[1] == 0]
    g = 0
    for r in rest: g = gcd(g, abs(r[0]))
    assert len(piv) == 1 and g > 0
    p = piv[0]
    if p[1] < 0: p = [-p[0], -p[1]]
    p = [p[0] % g, p[1]]
    return ((Fr(g, den), Fr(0)), (Fr(p[0], den), Fr(p[1], den)))

def span_mul(A, B, n): return hnf([mul(a, b, n) for a in A for b in B])
def scale(c, A, n): return hnf([mul(c, a, n) for a in A])

def mob(Mx, t, n):  # Möbius with rational matrix on t in K
    a, b, c, d = Mx
    num = (a*t[0] + b, a*t[1]); den = (c*t[0] + d, c*t[1])
    return mul(num, inv(den, n), n)

def matmul(X, Y):
    a, b, c, d = X; e, f, g, h = Y
    return (a*e + b*g, a*f + b*h, c*e + d*g, c*f + d*h)

W = (Fr(0), Fr(-1), Fr(32), Fr(0))
T4 = (Fr(1), Fr(1, 4), Fr(0), Fr(1))
T4i = (Fr(1), Fr(-1, 4), Fr(0), Fr(1))
gens = {'W': W, 'T': T4, 't': T4i}

def words(maxlen):
    yield '', (Fr(1), Fr(0), Fr(0), Fr(1))
    for L in range(1, maxlen + 1):
        for w in itertools.product('WTt', repeat=L):
            s = ''.join(w)
            if 'Tt' in s or 'tT' in s or 'WW' in s: continue
            M = (Fr(1), Fr(0), Fr(0), Fr(1))
            for ch in s: M = matmul(M, gens[ch])
            yield s, M

def homothetic(M1, M2, n, M1N, M2N):
    """find c with c*M2 = M1 and c*M2N = M1N, via Lagrange reduction of the norm form on M1."""
    covol = lambda B: abs(B[0][0]*B[1][1] - B[0][1]*B[1][0])
    target = covol(M1)/covol(M2)
    b1, b2 = list(M1[0]), list(M1[1])
    nf = lambda v: norm(tuple(v), n)
    dot = lambda u, v: u[0]*v[0] + n*u[1]*v[1]
    while True:
        if nf(b2) < nf(b1): b1, b2 = b2, b1
        mu = dot(b1, b2)/nf(b1)
        k = round(mu)
        if k == 0: break
        b2 = [b2[0]-k*b1[0], b2[1]-k*b1[1]]
    # reduced: enumerate i,j with nf(i b1 + j b2) == target
    import math
    B = int(math.isqrt(int(4*target/nf(b1)) + 4)) + 2
    for i in range(-B, B+1):
        for j in range(-B, B+1):
            c = (i*b1[0] + j*b2[0], i*b1[1] + j*b2[1])
            if c == (0, 0) or norm(c, n) != target: continue
            if scale(c, M2, n) == M1 and scale(c, M2N, n) == M1N:
                return c
    return None

def run(n, maxlen=6):
    m = (n + 1)//2
    w = (Fr(0), Fr(1))
    b = hnf([(Fr(m), Fr(0)), (Fr(-4), Fr(4))])
    tau = (Fr(1, 8*m), Fr(1, 8*m))
    LQ = hnf([(Fr(1), Fr(0)), tau]); LQN = hnf([(Fr(1, 32), Fr(0)), tau])
    found = []
    for s, M in words(maxlen):
        t2 = mob(M, tau, n)
        if t2[1] <= 0: continue
        L2 = hnf([(Fr(1), Fr(0)), t2]); L2N = hnf([(Fr(1, 32), Fr(0)), t2])
        c = homothetic(span_mul(b, L2, n), LQ, n, span_mul(b, L2N, n), LQN)
        if c is not None:
            found.append((s, t2, c))
            if len(found) >= 3: break
    return found

if __name__ == '__main__':
    for n in [5, 13, 21, 29, 37, 53, 61, 69, 77, 85]:
        f = run(n)
        print(n, [(s, t2, c) for s, t2, c in f])
        sys.stdout.flush()
