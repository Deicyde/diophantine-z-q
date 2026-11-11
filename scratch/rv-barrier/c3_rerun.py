"""Rerun of el-special C3 (route M), independent code.
Mechanism: m = m0 k^2, beta = sqf(m0 B), m0 B = beta g^2, t = (1/(beta l) - l)/2, Y = (1/(beta l) + l)/2,
k = g beta t / m0. Claims: (a) theta := m(m-B) and the point x = beta (beta t^2 + 1)^2 (k g / Y)^2 lies on
C_d, d = beta * theta, with x in beta Q*^2 (and (beta, 0) on C_beta); both curves y^2 = X^3 - d^2 X.
(b) for v_p(B) = -1 (m0 = 1), v_p(k) <= -1 for every lambda (paper proof: v(g) = -1, v(beta) = 1 and the
two terms of t have valuations of different parity, so v(t) <= -1).
Inputs: (a) 30 random (B, m0, lambda); (b) 30 random (p > 324, c, lambda)."""
import random
from fractions import Fraction as F
from sympy import factorint, integer_nthroot, prime
random.seed(11)
def sqf(x):
    x = F(x); n = x.numerator * x.denominator; r = -1 if n < 0 else 1
    for q, e in factorint(abs(n)).items():
        if e % 2: r *= q
    return r
def issq(x):
    x = F(x)
    return x >= 0 and integer_nthroot(x.numerator, 2)[1] and integer_nthroot(x.denominator, 2)[1]
def vp(x, p):
    x = F(x); n, d = x.numerator, x.denominator; e = 0
    while n % p == 0: n //= p; e += 1
    while d % p == 0: d //= p; e -= 1
    return e
def wit(B, m0, l):
    beta = sqf(m0 * B); g2 = m0 * B / beta
    g = F(integer_nthroot(g2.numerator, 2)[0], integer_nthroot(g2.denominator, 2)[0]); assert g * g == g2
    t = (1 / (beta * l) - l) / 2; Y = (1 / (beta * l) + l) / 2
    k = g * beta * t / m0; m = m0 * k * k; theta = m * (m - B)
    d = beta * theta; x = beta * (beta * t * t + 1) ** 2 * (k * g / Y) ** 2
    ok = x != 0 and d != 0 and issq(x ** 3 - d * d * x) and issq(x / beta) and beta**3 - beta**2 * beta == 0
    return ok, k
oka = 0
for i in range(30):
    B = F(random.randint(1, 10**7), random.randint(1, 3000) ** 2)
    m0 = random.choice([1, 2, 3, 5, 6, 7, 10, 13]); l = F(random.randint(1, 99), random.randint(1, 99))
    if sqf(m0 * B) * l * l == 1: continue
    ok, k = wit(B, m0, l); oka += ok
print("(a) explicit witnesses verified:", oka, "/ 30")
worst = -10**9; nb = 0
for i in range(30):
    p = prime(random.randint(67, 400)); c = random.choice([x for x in range(1, 200) if x % p])
    B = F(c, p); e = random.randint(-3, 3)
    l = F(random.randint(1, 500), random.randint(1, 500)) * F(p) ** e
    if sqf(B) * l * l == 1: continue
    ok, k = wit(B, 1, l); assert ok
    nb += 1; worst = max(worst, vp(k, p))
print("(b) inputs:", nb, "; max v_p(k) =", worst)
