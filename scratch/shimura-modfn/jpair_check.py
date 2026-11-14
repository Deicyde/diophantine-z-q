# Plane model (j(tau), j(N tau)) of X0(N) at Heegner points (N = 32): multiplicity of j(N tau)
# among the j-values of the psi(N) = 48 cyclic N-isogenous lattices (a tau + b)/d of <1, tau>,
# and the values x(tau), y(tau) of x0-32's eta quotients.  Plain Python complex (double precision).
# Usage: python3 -I jpair_check.py
import cmath, math
from math import gcd
def reduce(t):
    for _ in range(1000):
        t = complex(t.real - round(t.real), t.imag)
        if abs(t) < 1 - 1e-15: t = -1 / t
        else: return t
    return t
def sigma3(n): return sum(d**3 for d in range(1, n+1) if n % d == 0)
def jfun(t):
    t = reduce(t)
    if t.imag > 40: return complex(float('inf'), 0)  # |j| > 1e100: distinct from the finite values
    q = cmath.exp(2j*math.pi*t)
    E4 = 1 + 240*sum(sigma3(n)*q**n for n in range(1, 60))
    D = q
    for n in range(1, 200): D *= (1 - q**n)**24
    return E4**3 / D
def eta(t):
    q = cmath.exp(2j*math.pi*t); p = cmath.exp(2j*math.pi*t/24)
    for n in range(1, 4000):
        p *= (1 - q**n)
        if abs(q**n) < 1e-18: break
    return p
def xC(t): return eta(2*t)**2*eta(16*t)/(eta(4*t)*eta(32*t)**2) + 2
def yC(t): return -eta(8*t)**4*eta(16*t)**2/(eta(4*t)**2*eta(32*t)**4)
def check(A, B, C, N=32):
    D = B*B - 4*A*C
    tau = (-B + 1j*math.sqrt(-D)) / (2*A)
    j0, jN = jfun(tau), jfun(N*tau)
    vals = [jfun((a*tau + b)/(N//a)) for a in range(1, N+1) if N % a == 0
            for b in range(N//a) if gcd(gcd(a, b), N//a) == 1]
    mult = sum(1 for v in vals if math.isfinite(abs(v)) and abs(v - jN) < 1e-6*(1+abs(jN)))
    print(f'Q=[{A},{B},{C}] D={D} #isog={len(vals)} j(tau)={j0:.6f} j(N tau)={jN:.6f} '
          f'mult={mult} x={xC(tau):.10f} y={yC(tau):.10f}')
import sys
for Q in [(32,10,1), (32,-10,1), (32,18,3), (32,4,1), (64,12,1), (32,6,1), (96,-8,1)]:
    A, B, C = Q
    if B*B - 4*A*C < 0 and gcd(gcd(A, B), C) == 1: check(A, B, C)
print('sqrt(7) =', math.sqrt(7))
