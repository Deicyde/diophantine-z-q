# hx-used: check (Ix) x = 2 - 4 (p16(1/32) - p16(1/32 + t/8)) / (p16(3t/8) - p16(1/32 + t/8)),  p16 = wp of <1/16, t>,
# its 3t/8 variant, (IxW) x(-1/(32t)) = 2 - 4 (p2(t/2) - p2(t/2 + 1/16)) / (p2(3/16) - p2(t/2 + 1/16)),  p2 = wp of <1/2, t>,
# and (Iy) y = (x^3 + 4x + 16 - (x-2)^2 (x(-1/(32t)) + x + 2)) / 8, at 12 points of H (mpmath, 40 digits).
from mpmath import mp, mpf, mpc, exp, pi, jtheta
import random
mp.dps = 40
I = mpc(0, 1)

def eta(t):
    q = exp(2*pi*I*t); p = mpc(1); n = 1
    while True:
        term = q**n; p *= (1 - term)
        if abs(term) < mpf(10)**(-48): break
        n += 1
    return exp(pi*I*t/12)*p

def xC(t): return eta(2*t)**2*eta(16*t)/(eta(4*t)*eta(32*t)**2) + 2
def yC(t): return -eta(8*t)**4*eta(16*t)**2/(eta(4*t)**2*eta(32*t)**4)

def wp(z, T):
    q = exp(pi*I*T)
    t2 = jtheta(2, 0, q); t3 = jtheta(3, 0, q)
    return (pi*t2*t3*jtheta(4, pi*z, q)/jtheta(1, pi*z, q))**2 - pi**2/3*(t2**4 + t3**4)

def wpL(z, w1, t):  # lattice <w1, t> = w1 <1, t/w1>
    return wp(z/w1, t/w1)/w1**2

random.seed(1)
worst = [0, 0, 0, 0]
for i in range(12):
    t = mpc(random.uniform(-0.5, 0.5), random.uniform(0.35, 1.2))
    x, y = xC(t), yC(t)
    tw = -1/(32*t)
    xw = xC(tw)
    p16 = lambda z: wpL(z, mpf(1)/16, t)
    p2 = lambda z: wpL(z, mpf(1)/2, t)
    e1 = abs(x - (2 - 4*(p16(mpf(1)/32) - p16(mpf(1)/32 + t/8))/(p16(3*t/8) - p16(mpf(1)/32 + t/8))))/abs(x)
    e2 = abs(x - (2 - 4*(p16(mpf(1)/32) - p16(mpf(1)/32 + 3*t/8))/(p16(t/8) - p16(mpf(1)/32 + 3*t/8))))/abs(x)
    e3 = abs(xw - (2 - 4*(p2(t/2) - p2(t/2 + mpf(1)/16))/(p2(mpf(3)/16) - p2(t/2 + mpf(1)/16))))/abs(xw)
    e4 = abs(y - (x**3 + 4*x + 16 - (x - 2)**2*(xw + x + 2))/8)/abs(y)
    print(i, mp.nstr(t, 6), 'rel errors Ix, Ix(3t/8), IxW, Iy:', [mp.nstr(e, 3) for e in (e1, e2, e3, e4)])
    worst = [max(a, b) for a, b in zip(worst, (e1, e2, e3, e4))]
print('worst', [mp.nstr(e, 3) for e in worst])
