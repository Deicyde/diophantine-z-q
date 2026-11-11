"""Rerun of el-gadget E2 (column property), with edge cases el-gadget did not sample.
Toy of the test-site input over K0 = Q(sqrt2): R = R0 a^2, a = 1 - R0 q^2, tests C_j = D_j (in K0),
W = prod (1 + R C_j^2), Theta = Tr(W^{-1}) (rational), B = R / Theta^2.
30 data: p in primes > 324, v_p(R0) in {1, 3, -1}, one test with v_p < 0 so that the data is bad
at q = 0 (checked; for v_p(R0) = -1 any data is bad). 20 q per data, denominators p^e, e in 0..4,
and numerators divisible by p^f. Claim: bad (v_p(B) < 0 odd) for every q with B != 0."""
import random
from fractions import Fraction as F
from sympy import prime
random.seed(2026)
class K:
    def __init__(s, a, b=0): s.a = F(a); s.b = F(b)
    def __add__(s, o): o = o if isinstance(o, K) else K(o); return K(s.a + o.a, s.b + o.b)
    def __mul__(s, o): o = o if isinstance(o, K) else K(o); return K(s.a*o.a + 2*s.b*o.b, s.a*o.b + s.b*o.a)
    def inv(s): n = s.a*s.a - 2*s.b*s.b; return K(s.a/n, -s.b/n)
def vp(x, p):
    x = F(x)
    if x == 0: return None
    n, d = x.numerator, x.denominator; e = 0
    while n % p == 0: n //= p; e += 1
    while d % p == 0: d //= p; e -= 1
    return e
def B_of(R0, D, q):
    a = 1 - R0*q*q; R = R0*a*a
    W = K(1)
    for d in D: W = W * (K(1) + d*d*K(R))
    T = 2 * W.inv().a
    return None if T == 0 else R / (T*T)
bad_data = 0; pairs = 0; notbad = 0; edge = {1: 0, 3: 0, -1: 0}
for s in range(30):
    p = prime(random.randint(70, 300))
    e0 = [1, 3, -1][s % 3]
    u = random.choice([x for x in range(1, 60) if x % p])
    R0 = F(u) * F(p)**e0
    k0 = 3 if e0 == 3 else random.randint(1, 2)
    D = [K(F(random.randint(1, 30), p**k0), F(random.randint(0, 30), p**random.randint(0, k0)))]
    D += [K(random.randint(-20, 20), random.randint(-20, 20)) for _ in range(5)]
    b0 = B_of(R0, D, F(0))
    if b0 is None or not (vp(b0, p) < 0 and vp(b0, p) % 2): continue
    bad_data += 1; edge[e0] += 1
    for t in range(20):
        q = F(random.randint(1, 10**4) * p**random.randint(0, 2), p**random.randint(0, 4) * random.randint(1, 30))
        b = B_of(R0, D, q)
        if b is None or b == 0: continue
        pairs += 1
        if not (vp(b, p) < 0 and vp(b, p) % 2): notbad += 1
print("bad data:", bad_data, "by v_p(R0):", edge, "; (data,q) pairs:", pairs, "; pairs not bad:", notbad)
