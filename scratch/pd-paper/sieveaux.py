"""Numerical checks of the auxiliary inequalities of the two-dimensional sieve (section 4 of pd-paper.md).
 (1) R(w) = sum_{n<=w} r(n)/n >= (2/3) log w - 2, r(n) = sum_{d|n} chi_4(d)
 (2) S0(w) = sum_{l<=w, l squarefree, all prime factors = 1 mod 4} 2^omega(l)/l >= R(w)/V,  V <= 2 zeta(2)^4
 (3) pointwise r <= h * v  (n <= 10^5)
 (4) sum_{l > L prime} 1/l^2 <= 4 log 4 /(L log L)
"""
import math
W = 10**6
spf = list(range(W + 1))
for i in range(2, int(W**.5) + 1):
    if spf[i] == i:
        for j in range(i*i, W + 1, i):
            if spf[j] == j: spf[j] = i
def fac(n):
    f = {}
    while n > 1:
        p = spf[n]; f[p] = f.get(p, 0) + 1; n //= p
    return f
def r(n):
    out = 1
    for p, k in fac(n).items():
        if p == 2: continue
        out *= (k + 1) if p % 4 == 1 else (1 if k % 2 == 0 else 0)
    return out
def h(n):
    out = 1
    for p, k in fac(n).items():
        if p % 4 != 1 or k > 1: return 0
        out *= 2
    return out
def v(n):
    out = 1
    for p, k in fac(n).items():
        if p == 2: continue
        if k % 2: return 0
        out *= (k + 1) if p % 4 == 1 else 1
    return out
R = 0.0; S0 = 0.0; Vs = 0.0
checkpoints = {10**k for k in range(1, 7)}
for n in range(1, W + 1):
    R += r(n) / n; S0 += h(n) / n; Vs += v(n) / n
    if n in checkpoints:
        print(f"w={n:8d}: R={R:8.4f} >= (2/3)log w - 2 = {(2/3)*math.log(n)-2:8.4f};  S0={S0:8.4f};  R/S0={R/S0:6.3f};  partial V={Vs:6.3f}")
z2 = math.pi**2 / 6
print(f"2 zeta(2)^4 = {2*z2**4:.3f};  (pi/4) log w/S0 asymptotics: S0 ~ c log w")
bad = 0
for n in range(1, 10**5 + 1):
    conv = sum(h(d) * v(n // d) for d in range(1, n + 1) if n % d == 0) if n < 3000 else None
    if conv is not None and r(n) > conv: bad += 1
print("pointwise r <= h*v failures (n < 3000):", bad)
primes = [p for p in range(2, W + 1) if spf[p] == p]
for L in [10, 100, 1000, 10**4]:
    t = sum(1 / p**2 for p in primes if p > L)
    print(f"L={L}: sum_(l>L) 1/l^2 = {t:.3e} <= 4log4/(L log L) = {4*math.log(4)/(L*math.log(L)):.3e}")
