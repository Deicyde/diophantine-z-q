# X3a: local criterion for the M1 theta=1 curve  C: Y^2 = f(q) = m^2 T^2 - m R0 (1 - R0 q^2)^2
# at an odd prime p | num(T), p !| 2 m R0, (R0/p) = -1. Claim: C(Q_p) != {} iff (-m/p) = -1.
from fractions import Fraction as Fr
import random, itertools
random.seed(2)
def vp(x, p):
    x = Fr(x); 
    if x == 0: return 10**9
    v = 0; n, d = x.numerator, x.denominator
    while n % p == 0: n //= p; v += 1
    while d % p == 0: d //= p; v -= 1
    return v
def unit(x, p):
    x = Fr(x); v = vp(x, p); return x / Fr(p)**v if v >= 0 else x * Fr(p)**(-v)
def leg(a, p):
    a %= p; return 0 if a == 0 else (1 if pow(a, (p-1)//2, p) == 1 else -1)
def is_sq_Qp(x, p):
    if x == 0: return True
    v = vp(x, p)
    if v % 2: return False
    u = unit(x, p); return leg(u.numerator * pow(u.denominator, -1, p), p) == 1
def locsol(m, R0, T, p, K=3):
    f = lambda q: m*m*T*T - m*R0*(1 - R0*q*q)**2
    g = lambda r: m*m*T*T*r**4 - m*R0*(r*r - R0)**2       # r^4 f(1/r)
    mod = p**K
    for q in range(mod):                                   # q in Z_p, to precision p^K
        y = f(Fr(q))
        if y == 0 or (vp(y, p) < K - 1 and is_sq_Qp(y, p)): return True
    for r in range(0, mod, p):                             # q = 1/r, r in pZ_p
        y = g(Fr(r))
        if y == 0 or (vp(y, p) < K - 1 and is_sq_Qp(y, p)): return True
    return False
agree = tot = 0
for p in [11, 13, 17, 19, 23]:
    for trial in range(6):
        m = random.choice([1, 2, 3, 5, 6, 7, -1, -3])
        if m % p == 0: continue
        while True:
            R0 = Fr(random.randint(2, 500), random.randint(1, 20))
            if vp(R0, p) == 0 and leg(R0.numerator * R0.denominator, p) == -1: break
        T = Fr(p * random.randint(1, 50), random.randint(1, 30))
        if vp(T, p) <= 0: continue
        pred = (leg(-m, p) == -1)
        got = locsol(Fr(m), R0, T, p)
        tot += 1; agree += (pred == got)
print("X3a criterion agreement:", agree, "/", tot)
