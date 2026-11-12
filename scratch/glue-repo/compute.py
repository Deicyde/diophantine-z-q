"""glue-repo exact computations (sympy). Run: ~/pyenv/bin/python -I scratch/glue-repo/compute.py"""
import sympy as sp
from sympy import symbols, expand, Poly, factorint, gcdex, resultant, discriminant
u = symbols('u')
F = u*(u+15)*(u+20)*(u+24)*(u+30)*(u+60)
G = 7*u**2 + 300*u + 3600
H = (u**2-60*u-1800)*(13*u**2+480*u+3600)*(11*u**2+600*u+7200)
# 1. Rosati positivity: Trd(a mu^-1 abar mu) as quadratic form in a = x0 + x1 i + x2 j + x3 ij, B=(2,-3)
A_, B_ = 2, -3
def mul(x, y):
    x0,x1,x2,x3 = x; y0,y1,y2,y3 = y
    return (x0*y0 + A_*x1*y1 + B_*x2*y2 - A_*B_*x3*y3,
            x0*y1 + x1*y0 - B_*x2*y3 + B_*x3*y2,
            x0*y2 + x2*y0 + A_*x1*y3 - A_*x3*y1,
            x0*y3 + x3*y0 + x1*y2 - x2*y1)
conj = lambda x: (x[0], -x[1], -x[2], -x[3])
x = symbols('x0:4')
mu = (0,0,2,1); mui = tuple(sp.Rational(-1,6)*c for c in mu)
assert [expand(c) for c in mul(mu,mu)] == [-6,0,0,0]
q = expand(2*mul(mul(mul(x, mui), conj(x)), mu)[0])
print("Trd(a mu^-1 abar mu) =", q)
M = sp.hessian(q, x)/2
print("Gram:", M.tolist(), "leading minors:", [M[:k,:k].det() for k in range(1,5)])
# 2. resultant / Bezout certificates
for (n1,P1),(n2,P2) in [(("F",F),("G",G)),(("F",F),("H",H)),(("G",G),("H",H))]:
    s,t,g = gcdex(Poly(P1,u,domain='QQ'), Poly(P2,u,domain='QQ'))
    den = sp.ilcm(*[c.q for c in s.all_coeffs()+t.all_coeffs()])
    print(n1,n2,"Res primes", factorint(resultant(P1,P2,u)), "Bezout denominator", factorint(den))
# 3. elements of O with trd 0, nrd 3: is (1+x)/2 in O?  x = a + b i + c(1+j)/2 + d(i+ij)/2
a,b,c,d = symbols('a b c d', integer=True)
X = (a + c*sp.Rational(1,2), b + d*sp.Rational(1,2), c*sp.Rational(1,2), d*sp.Rational(1,2))
nrdX = expand(X[0]**2 - A_*X[1]**2 - B_*X[2]**2 + A_*B_*X[3]**2)
print("trd =", 2*X[0], " nrd =", nrdX)
import itertools
bad = []
for (aa,bb,cc,dd) in itertools.product(range(-12,13), repeat=4):
    if 2*aa+cc == 0 and nrdX.subs({a:aa,b:bb,c:cc,d:dd}) == 3:
        # (1+x)/2 coords: (1+x)/2 = (1+a)/2 + b/2 i + c/2 e3 + d/2 e4 ; integral iff 1+a, b, c, d even
        if not ((1+aa)%2==0 and bb%2==0 and cc%2==0 and dd%2==0): bad.append((aa,bb,cc,dd))
print("type (0,3) elements in box with (1+x)/2 not in O:", bad[:5])
# 4. structure constants of O in the basis (1, i, (1+j)/2, (i+ij)/2)
n = symbols('n0:4'); m = symbols('m0:4')
basis = [(1,0,0,0),(0,1,0,0),(sp.Rational(1,2),0,sp.Rational(1,2),0),(0,sp.Rational(1,2),0,sp.Rational(1,2))]
comb = lambda v: tuple(sum(v[t]*basis[t][s] for t in range(4)) for s in range(4))
coordsO = lambda q: (q[0]-q[2], q[1]-q[3], 2*q[2], 2*q[3])
P = mul(comb(n), comb(m))
print("coords of product:", [expand(c) for c in coordsO(P)])
# 5. Rosati involution in O-coordinates
R = mul(mul(mui, conj(comb(n))), mu)
print("coords of ros(comb n):", [expand(c) for c in coordsO(R)])
# 6. trace form of O
print("Trd(e_a e_b):", [[2*mul(basis[s],basis[t])[0] for t in range(4)] for s in range(4)])
