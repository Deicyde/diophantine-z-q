# y3-x6: exact check of diophantine_zq.tex L511-519 (pullback of Y3 -> P^1_j along J(u) = -57600 F^2 / G^6).
from fractions import Fraction as Fr
def mul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): r[i + j] += x * y
    return r
def add(a, b):
    n = max(len(a), len(b)); a = a + [0] * (n - len(a)); b = b + [0] * (n - len(b))
    return [x + y for x, y in zip(a, b)]
def sc(c, a): return [c * x for x in a]
def pw(a, k):
    r = [1]
    for _ in range(k): r = mul(r, a)
    return r
def trim(a):
    while len(a) > 1 and a[-1] == 0: a = a[:-1]
    return a
F = [1]
for c in [0, 15, 20, 24, 30, 60]: F = mul(F, [c, 1])
G = [3600, 300, 7]
H = mul(mul([-1800, -60, 1], [3600, 480, 13]), [7200, 600, 11])
lhs = trim(add(pw(G, 6), sc(-97200, mul(F, F))))
rhs = trim(mul(H, H))
print('G^6 - 97200 F^2 == H^2:', lhs == rhs)
print('57600*27/16 =', Fr(57600 * 27, 16))
# J + 16/27 = 16 (G^6 - 97200 F^2) / (27 G^6)
num = add(sc(-57600 * 27, mul(F, F)), sc(16, pw(G, 6)))
print('27 G^6 (J + 16/27) == 16 H^2:', trim(num) == trim(sc(16, mul(H, H))))
# discriminants / resultants: prime support of the pairwise resultants of the six linear factors, G, and the three quadratics of H
def res_lin_poly(c, P):  # resultant of (u + c) and P = P(-c) up to sign
    return sum(x * (-c) ** i for i, x in enumerate(P))
def factor(n):
    n = abs(n); ps = set(); d = 2
    while d * d <= n:
        while n % d == 0: ps.add(d); n //= d
        d += 1
    if n > 1: ps.add(n)
    return ps
quads = {'G': G, 'H1': [-1800, -60, 1], 'H2': [3600, 480, 13], 'H3': [7200, 600, 11]}
sup = set()
cs = [0, 15, 20, 24, 30, 60]
for i in range(6):
    for j in range(i + 1, 6): sup |= factor(cs[i] - cs[j])
    for q in quads.values(): sup |= factor(res_lin_poly(cs[i], q))
def disc(q): return q[1] ** 2 - 4 * q[0] * q[2]
def res_qq(p, q):  # resultant of two quadratics a0+a1x+a2x^2 via Sylvester determinant
    a0, a1, a2 = p; b0, b1, b2 = q
    M = [[a2, a1, a0, 0], [0, a2, a1, a0], [b2, b1, b0, 0], [0, b2, b1, b0]]
    def det(m):
        if len(m) == 1: return m[0][0]
        return sum((-1) ** k * m[0][k] * det([r[:k] + r[k + 1:] for r in m[1:]]) for k in range(len(m)))
    return det(M)
for n, q in quads.items(): sup |= factor(disc(q)); sup |= factor(q[2])
ks = list(quads)
for i in range(len(ks)):
    for j in range(i + 1, len(ks)): sup |= factor(res_qq(quads[ks[i]], quads[ks[j]]))
print('prime support of discriminants/resultants/leading coefficients:', sorted(sup))
