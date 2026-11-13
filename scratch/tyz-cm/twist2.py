exec(open('twist.py').read().split("T00 = ")[0].replace("for n in [5,13,21]:","for n in []:"))
from math import gcd
T00 = (mpf(0), mpf(0))
def reduce0(z, N=32, cmax=4000):
    best = (z.imag, 0, 1)
    for c in range(N, cmax, N):
        d0 = int(-(c*z.real))
        for d in range(d0-3, d0+4):
            if gcd(c,d) != 1: continue
            im = z.imag/abs(c*z+d)**2
            if im > best[0]: best = (im, c, d)
    im, c, d = best
    if c == 0: return z, None
    # find a,b with ad - bc = 1
    import sympy
    a, b0, g = sympy.gcdex(d, -c); assert g == 1
    a, b = int(a), int(b0)
    return (a*z+b)/(c*z+d), (a,b,c,d)
def dist(P,Q): return abs(P[0]-Q[0])+abs(P[1]-Q[1])
for n in [5, 13, 21, 29, 37, 45, 53, 61, 69, 77, 85, 93, 101, 109, 133, 141, 165, 205]:
    M, MN, tau = run(n)
    u = M[0][0]; v = M[1]
    w = I*sqrt(n)
    taup = (v[0] + v[1]*w)/u
    z, g = reduce0(taup)
    P = phi(tau); Pp = phi(z)
    S = add(P, T00)
    print(n, "Im tau'", float(taup.imag), "-> ", float(z.imag), g, " d(phi tau', phi tau + (0,0)) =", float(dist(Pp,S)), " d(phi tau', phi tau)=", float(dist(Pp,P)))
