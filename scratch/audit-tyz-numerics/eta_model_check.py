# Independent check (exact integer q-expansions) of the eta-quotient model used by the Lean file X0.lean:
#   x = eta(2t)^2 eta(16t) / (eta(4t) eta(32t)^2) + 2,  y = - eta(8t)^4 eta(16t)^2 / (eta(4t)^2 eta(32t)^4)
#   f = eta(4t)^2 eta(8t)^2
# Claims: y^2 = x^3 + 4x ;  q dx/dq = 2 f y  (i.e. dx/(2y) = 2 pi i f dtau).
N = 400  # number of q-coefficients kept (relative to leading power)

def mul(a, b):
    c = [0]*N
    for i, ai in enumerate(a):
        if ai == 0: continue
        for j, bj in enumerate(b):
            if i + j >= N: break
            if bj: c[i+j] += ai*bj
    return c

def euler(d):  # prod_{n>=1} (1 - q^{d n})  as list
    c = [0]*N; c[0] = 1
    n = 1
    while d*n < N:
        # multiply by (1 - q^{dn})
        k = d*n
        for i in range(N-1, k-1, -1):
            c[i] -= c[i-k]
        n += 1
    return c

def inv(a):  # power series inverse, a[0] = 1
    b = [0]*N; b[0] = 1
    for n in range(1, N):
        s = 0
        for k in range(1, n+1):
            if a[k]: s += a[k]*b[n-k]
        b[n] = -s
    return b

def pw(a, k):
    r = [0]*N; r[0] = 1
    for _ in range(k): r = mul(r, a)
    return r

E = {d: euler(d) for d in (2, 4, 8, 16, 32)}
Ei = {d: inv(E[d]) for d in (4, 32)}
# x - 2 = q^{-2} * X0 ; y = -q^{-3} * Y0 ; f = q * F0
X0 = mul(mul(pw(E[2],2), E[16]), mul(Ei[4], pw(Ei[32],2)))
Y0 = mul(mul(pw(E[8],4), pw(E[16],2)), mul(pw(Ei[4],2), pw(Ei[32],4)))
F0 = mul(pw(E[4],2), pw(E[8],2))
# Laurent series as dict exponent->coeff, truncated at exponent < M
def laurent(coefs, shift):
    return {i+shift: c for i, c in enumerate(coefs) if c}
def ladd(a, b, sb=1):
    r = dict(a)
    for k, v in b.items(): r[k] = r.get(k, 0) + sb*v
    return {k: v for k, v in r.items() if v}
def lmul(a, b, M):
    r = {}
    for i, ai in a.items():
        for j, bj in b.items():
            if i + j < M: r[i+j] = r.get(i+j, 0) + ai*bj
    return {k: v for k, v in r.items() if v}
x = ladd(laurent(X0, -2), {0: 2})
y = {k: -v for k, v in laurent(Y0, -3).items()}
f = laurent(F0, 1)
M = N - 10
lhs = lmul(y, y, M)
x2 = lmul(x, x, M + 3); x3 = lmul(x2, x, M)
rhs = ladd(x3, {k: 4*v for k, v in x.items() if k < M})
diff = ladd(lhs, rhs, -1)
print("x leading terms:", sorted(x.items())[:6])
print("y leading terms:", sorted(y.items())[:6])
print("f leading terms:", sorted(f.items())[:8])
print("y^2 - (x^3+4x): nonzero coefficients below q^%d:" % M, {k: v for k, v in diff.items() if k < M})
# q dx/dq = 2 f y
qdx = {k: k*v for k, v in x.items() if k}
fy2 = {k: 2*v for k, v in lmul(f, y, M).items()}
d2 = ladd(qdx, fy2, -1)
print("q dx/dq - 2 f y: nonzero coefficients below q^%d:" % (M-5), {k: v for k, v in d2.items() if k < M-5})
