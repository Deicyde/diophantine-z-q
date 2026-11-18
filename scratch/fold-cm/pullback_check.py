# fold-cm: exact check of diophantine_zq.tex L511-519 with F, G from L381-383 (pure Python; no sympy on this host).
from fractions import Fraction
def mul(a, b):
    r = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): r[i+j] += x*y
    return r
def add(a, b, s=1):
    n = max(len(a), len(b)); a = a+[0]*(n-len(a)); b = b+[0]*(n-len(b))
    return [x+s*y for x, y in zip(a, b)]
def prod(fs):
    r = [1]
    for f in fs: r = mul(r, f)
    return r
def pw(a, k): return prod([a]*k)
# coefficient lists, lowest degree first
lin = lambda c: [c, 1]
facsF = [lin(0), lin(15), lin(20), lin(24), lin(30), lin(60)]
F = prod(facsF); G = [3600, 300, 7]
Hf = [[-1800, -60, 1], [3600, 480, 13], [7200, 600, 11]]
H = prod(Hf)
D = add(add(pw(G, 6), [97200*c for c in mul(F, F)], -1), mul(H, H), -1)
print("G^6 - 97200 F^2 - H^2 == 0:", all(c == 0 for c in D))
def det(M):
    M = [[Fraction(x) for x in row] for row in M]; n = len(M); d = Fraction(1)
    for i in range(n):
        p = next((k for k in range(i, n) if M[k][i] != 0), None)
        if p is None: return 0
        if p != i: M[i], M[p] = M[p], M[i]; d = -d
        d *= M[i][i]
        for k in range(i+1, n):
            f = M[k][i]/M[i][i]
            M[k] = [x - f*y for x, y in zip(M[k], M[i])]
    return d
def res(a, b):
    m, n = len(a)-1, len(b)-1; A = a[::-1]; B = b[::-1]; S = []
    for i in range(n): S.append([0]*i + A + [0]*(n-1-i))
    for i in range(m): S.append([0]*i + B + [0]*(m-1-i))
    return int(det(S))
def primes(n):
    n = abs(n); p = 2; s = set()
    while p*p <= n:
        while n % p == 0: s.add(p); n //= p
        p += 1
    if n > 1: s.add(n)
    return s
facs = facsF + [G] + Hf
P = set()
for f in facs:
    if len(f) == 3: P |= primes(f[1]**2 - 4*f[0]*f[2])
    P |= primes(f[-1])
for i in range(len(facs)):
    for j in range(i+1, len(facs)):
        r = res(facs[i], facs[j]); assert r != 0
        P |= primes(r)
print("prime support (discriminants, leading coefficients, pairwise resultants):", sorted(P))
print("J(inf) = -57600/7^6 =", Fraction(-57600, 7**6), "; branch values 0, inf, -16/27:", Fraction(-57600, 7**6) != Fraction(-16, 27))
