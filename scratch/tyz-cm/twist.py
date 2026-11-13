# Numerics for TYZSigmaFixesZn: alpha-twist at 2 of TYZ's Heegner pair, phi values.
import sys
from mpmath import mp, mpf, mpc, exp, pi, sqrt, matrix
from fractions import Fraction as Fr
from sympy import Matrix, ZZ
from sympy.matrices.normalforms import hermite_normal_form
mp.dps = 40
I = mpc(0,1)
def eta(z, terms=400):
    q = exp(2*pi*I*z)
    p = exp(2*pi*I*z/24)
    for k in range(1,20000):
        p *= (1 - q**k)
        if abs(q**k) < mpf(10)**(-45): break
    return p
def phi(z):
    e = lambda d: eta(d*z)
    x = e(2)**2*e(16)/(e(4)*e(32)**2) + 2
    y = -(e(8)**4*e(16)**2/(e(4)**2*e(32)**4))
    return x, y
def add(P, Q):
    if P is None: return Q
    if Q is None: return P
    (x1,y1),(x2,y2) = P,Q
    if abs(x1-x2) < 1e-25:
        if abs(y1+y2) < 1e-25: return None
        l = (3*x1**2+4)/(2*y1)
    else:
        l = (y2-y1)/(x2-x1)
    x3 = l**2 - x1 - x2
    y3 = -(l*(x3-x1)+y1)
    return (x3,y3)
# K-elements as pairs (a,b) = a + b*w, w^2 = -n, rational
def run(n):
    w = I*sqrt(n)
    # tau = (1+w)/24 root of [16(n+1), -8, 1]?  check
    A,B,C = 16*(n+1), -8, 1
    tau = (-B + I*sqrt(64*n))/(2*A)
    assert abs(A*tau**2+B*tau+C) < 1e-30
    # lattice elements as vectors over Q-basis (1, w): tau = (8 + 8w)/(2A) = (1+w)/(4(n+1))
    t = (Fr(1,4*(n+1)), Fr(1,4*(n+1)))
    def mul(u,v): return (u[0]*v[0]-n*u[1]*v[1], u[0]*v[1]+u[1]*v[0])
    bbar = [(Fr(6),Fr(-4)), (Fr(3-4*n),Fr(-8))]   # conj of b cap O4 = <6+4w, 3-4n+8w>
    L  = [(Fr(1),Fr(0)), t]
    LN = [(Fr(1,32),Fr(0)), t]
    def span(gens):
        den = 1
        for g in gens:
            for c in g: den = den*c.denominator//__import__('math').gcd(den,c.denominator)
        M = Matrix([[int(g[0]*den), int(g[1]*den)] for g in gens])
        H = hermite_normal_form(M.T).T  # rows basis
        rows = [ (Fr(int(H[i,0]),den), Fr(int(H[i,1]),den)) for i in range(H.rows) if any(H[i,j]!=0 for j in range(2))]
        return rows
    M  = span([mul(b,l) for b in bbar for l in L])
    MN = span([mul(b,l) for b in bbar for l in LN])
    return M, MN, tau
for n in [5,13,21]:
    M, MN, tau = run(n)
    print(n, "bbar*L basis", M, "bbar*LN basis", MN)

T00 = (mpf(0), mpf(0))
for n in [5, 13, 21, 29, 37]:
    M, MN, tau = run(n)
    u = M[0][0]; v = M[1]
    w = I*sqrt(n)
    taup = (v[0] + v[1]*w)/u
    # check LN condition: MN == < u/32, v > as lattices
    P = phi(tau); Pp = phi(taup)
    S = add(P, T00)
    # i-action: [i](x,y) = (-x, i y)
    iP = (-P[0], I*P[1])
    print(n, "tau'=", (v[0]/u, v[1]/u), "MN", MN)
    print("  phi(tau') - (phi(tau)+(0,0)):", abs(Pp[0]-S[0]), abs(Pp[1]-S[1]), " vs phi(tau):", abs(Pp[0]-P[0]), abs(Pp[1]-P[1]))
    for name, Q in [("-P", (P[0], -P[1])), ("iP", iP), ("-iP", (iP[0], -iP[1]))]:
        R = add(Q, T00)
        print("   ", name, abs(Pp[0]-Q[0])+abs(Pp[1]-Q[1]), name+"+T00", abs(Pp[0]-R[0])+abs(Pp[1]-R[1]))
