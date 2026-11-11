"""Rerun of el-special C5 (Lemma G Cor 2), independent code and different primes; adds M = 0.
Toy test site: F(n) = prod_{c in C}(n - c), C = {0,-15,-20,-24,-30,-60}, R0 = 2730^6 |F(n)|,
a = 1 - R0 q^2, R = R0 a^2, C_j = D_j / F(n) with D_j fixed in Q(sqrt2), W = prod(1 + R C_j^2),
Theta = Tr W^{-1}, B = R/Theta^2. Curve: n = c + lam, q = q0 lam^{-M}; evaluate at lam = p.
Prediction (paper): v_p(B) = 15 - 52M for M >= 1; for M = 0 (q fixed, p-integral): 1 - 12 = -11.
30 inputs: p in {10007, 100003, 1000033}, c in C (cycled), M in {0,1,2,3} (cycled), random q0, D_j."""
import random
from fractions import Fraction as F
random.seed(99)
CC = [0, -15, -20, -24, -30, -60]
class K:
    def __init__(s, a, b=0): s.a = F(a); s.b = F(b)
    def __add__(s, o): o = o if isinstance(o, K) else K(o); return K(s.a + o.a, s.b + o.b)
    def __mul__(s, o): o = o if isinstance(o, K) else K(o); return K(s.a*o.a + 2*s.b*o.b, s.a*o.b + s.b*o.a)
    def inv(s): n = s.a*s.a - 2*s.b*s.b; return K(s.a/n, -s.b/n)
def vp(x, p):
    x = F(x); n, d = x.numerator, x.denominator; e = 0
    while n % p == 0: n //= p; e += 1
    while d % p == 0: d //= p; e -= 1
    return e
ok = 0; tot = 0; rows = []
for i in range(30):
    p = [10007, 100003, 1000033][i % 3]; c = CC[i % 6]; M = i % 4
    lam = F(p); n = c + lam; Fn = F(1)
    for cc in CC: Fn *= (n - cc)
    R0 = F(2730) ** 6 * abs(Fn)
    q = F(random.randint(1, 999), random.randint(1, 999)) / lam ** M
    a = 1 - R0 * q * q; R = R0 * a * a
    W = K(1)
    for _ in range(6):
        d = K(random.randint(1, 99), random.randint(1, 99)); Cj = d * K(1 / Fn)
        W = W * (K(1) + Cj * Cj * K(R))
    T = 2 * W.inv().a; B = R / (T * T)
    pred = 15 - 52 * M if M >= 1 else -11
    got = vp(B, p); tot += 1; ok += (got == pred); rows.append((p, c, M, got, pred))
for r in rows[:8]: print(r)
print("matches:", ok, "/", tot)
