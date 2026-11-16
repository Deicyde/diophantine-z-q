# hx-used: search weight-0 expressions of x0-32's x, y in Weierstrass values of L16 = <1/16, tau>
# at points of E16[4]  (mpmath, 40 digits).
import itertools
from mpmath import mp, mpf, mpc, exp, pi, jtheta, nprod, inf
mp.dps = 40
import sys
MM = int(sys.argv[1]) if len(sys.argv) > 1 else 4
I = mpc(0, 1)

def eta(t):
    q = exp(2*pi*I*t)
    p = mpc(1)
    n = 1
    while True:
        term = q**n
        p *= (1 - term)
        if abs(term) < mpf(10)**(-45):
            break
        n += 1
    return exp(pi*I*t/12)*p

def xC(t):
    return eta(2*t)**2*eta(16*t)/(eta(4*t)*eta(32*t)**2) + 2

def yC(t):
    return -eta(8*t)**4*eta(16*t)**2/(eta(4*t)**2*eta(32*t)**4)

def wp(z, T):
    # Weierstrass p for lattice Z + Z T
    q = exp(pi*I*T)
    t2 = jtheta(2, 0, q); t3 = jtheta(3, 0, q)
    return (pi*t2*t3*jtheta(4, pi*z, q)/jtheta(1, pi*z, q))**2 - pi**2/3*(t2**4 + t3**4)

def wp16(z, t):
    # lattice <1/16, t> = (1/16) <1, 16 t>
    return 256*wp(16*z, 16*t)

# sanity: Laurent constant term of wp is 0, e1+e2+e3 = 0
T = mpc('0.1', '1.1')
z = mpf(10)**-8
print('laurent const', abs(wp(z, T) - 1/z**2))
print('e sum', abs(wp(mpf(1)/2, T) + wp(T/2, T) + wp((1+T)/2, T)))

taus = [mpc('0.1', '1.3'), mpc('-0.23', '0.71'), mpc('0.31', '0.9')]
res = {}
for t in taus:
    pts = {}
    for a in range(MM):
        for b in range(MM):
            if (a, b) == (0, 0):
                continue
            pts[(a, b)] = wp16(mpf(a)/(16*MM) + b*t/MM, t)
    x, y = xC(t), yC(t)
    print('curve eq residual', abs(y**2 - x**3 - 4*x))
    res[t] = (x, y, pts)

def neg(k):
    return ((-k[0]) % MM, (-k[1]) % MM)
keys = []
for k in res[taus[0]][2].keys():
    if neg(k) not in keys:
        keys.append(k)
print('points mod +-:', keys)
for target in ['x', 'x/2', 'x-2', 'y']:
    for p1, p2, p3 in itertools.permutations(keys, 3):
        vals = []
        for t in taus:
            x, y, pts = res[t]
            r = (pts[p1] - pts[p2])/(pts[p3] - pts[p2])
            tv = {'x': x, 'x/2': x/2, 'x-2': x-2, 'y': y}[target]
            vals.append(r / tv)
        if abs(vals[0]) > mpf(10)**-10 and all(abs(v - vals[0]) < mpf(10)**-25 for v in vals):
            print(target, '= c *', (p1, p2, p3), 'c =', mp.nstr(vals[0], 15))
