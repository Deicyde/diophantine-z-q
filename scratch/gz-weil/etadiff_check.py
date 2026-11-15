# Independent exact check of x0-32's EtaModelDifferential: q dx/dq = 2 y f  (x' = 4 pi i f y),
# and of the chain f = sum heckeCoeff 1 n q^n (theta series of the Hecke character of Q(i)).
# x = eta(2t)^2 eta(16t) / (eta(4t) eta(32t)^2) + 2, y = -eta(8t)^4 eta(16t)^2/(eta(4t)^2 eta(32t)^4),
# f = eta(4t)^2 eta(8t)^2. Laurent series in q with integer coefficients, truncated.
N = 120
def eta_prod(d, N):  # prod (1-q^{dn}) as list of coefficients up to q^N (without q^{d/24})
    c = [0]*(N+1); c[0] = 1
    n = 1
    while d*n <= N:
        new = c[:]
        for i in range(N+1-d*n):
            new[i+d*n] -= c[i]
        c = new; n += 1
    return c
def mul(a, b):
    c = [0]*(N+1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b[:N+1-i]):
                c[i+j] += x*y
    return c
def inv(a):  # a[0] = 1
    b = [0]*(N+1); b[0] = 1
    for n in range(1, N+1):
        b[n] = -sum(a[k]*b[n-k] for k in range(1, n+1))
    return b
def pw(a, k):
    r = [1]+[0]*N
    for _ in range(k): r = mul(r, a)
    return r
E = {d: eta_prod(d, N) for d in (2, 4, 8, 16, 32)}
# x: q-power: (2*2 + 16 - 4 - 2*32)/24 = -48/24 = -2
xs = mul(mul(pw(E[2], 2), E[16]), inv(mul(E[4], pw(E[32], 2))))  # times q^-2, then + 2
# y: q-power (8*4 + 16*2 - 4*2 - 32*4)/24 = (32+32-8-128)/24 = -3
ys = [-c for c in mul(mul(pw(E[8], 4), pw(E[16], 2)), inv(mul(pw(E[4], 2), pw(E[32], 4))))]
# f: q-power (4*2+8*2)/24 = 1
fs = mul(pw(E[4], 2), pw(E[8], 2))
# Represent Laurent series as dict exponent->coeff
X = {k-2: v for k, v in enumerate(xs)}; X[0] = X.get(0, 0) + 2
Y = {k-3: v for k, v in enumerate(ys)}
F = {k+1: v for k, v in enumerate(fs)}
qdX = {k: k*v for k, v in X.items()}
YF = {}
for a, u in Y.items():
    for b, v in F.items():
        YF[a+b] = YF.get(a+b, 0) + 2*u*v
ok = all(qdX.get(k, 0) == YF.get(k, 0) for k in range(-2, N-6))
print("q dx/dq == 2 y f up to q^%d:" % (N-7), ok)
# y^2 = x^3 + 4x
def lmul(A, B):
    C = {}
    for a, u in A.items():
        for b, v in B.items():
            C[a+b] = C.get(a+b, 0) + u*v
    return C
Y2 = lmul(Y, Y); X3 = lmul(lmul(X, X), X)
ok2 = all(Y2.get(k, 0) == X3.get(k, 0) + 4*X.get(k, 0) for k in range(-6, N-10))
print("y^2 == x^3 + 4x up to q^%d:" % (N-11), ok2)
# heckeCoeff 1 n = (1/4) sum_{a^2+b^2=n} unitOf(a,b) (a+bi)
def unitOf(a, b):
    t = (a % 4, b % 4)
    if t in [(1, 0), (3, 2)]: return 1
    if t in [(3, 0), (1, 2)]: return -1
    if t in [(0, 3), (2, 1)]: return 1j
    if t in [(0, 1), (2, 3)]: return -1j
    return 0
def hecke(n):
    s = 0
    r = int(n**0.5)+1
    for a in range(-r, r+1):
        for b in range(-r, r+1):
            if a*a+b*b == n: s += unitOf(a, b)*complex(a, b)
    return s/4
ok3 = all(abs(hecke(n) - F.get(n, 0)) < 1e-9 for n in range(1, N))
print("f = sum heckeCoeff 1 n q^n up to q^%d:" % (N-1), ok3)
