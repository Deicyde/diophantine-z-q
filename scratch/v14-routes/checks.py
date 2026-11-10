# Exact checks in Q(sqrt2) for v14-routes (elements a+b*s as pairs of Fractions).
from fractions import Fraction as F
def m(x,y): return (x[0]*y[0]+2*x[1]*y[1], x[0]*y[1]+x[1]*y[0])
def a(x,y): return (x[0]+y[0], x[1]+y[1])
def neg(x): return (-x[0],-x[1])
def sub(x,y): return a(x,neg(y))
def N(x): return x[0]**2-2*x[1]**2
def pw(x,k):
    r=(F(1),F(0))
    for _ in range(k): r=m(r,x)
    return r
eps=(F(1),F(1))                       # 1+s
d_main=(F(75),F(-53)); d_q=(F(3),F(-1))
D=m(d_q,d_q)
print("D =",D, " (expect 11-6s)")
# main curve E: y^2=x^3-d_main^2 x ; quartic curve y^2=x^3-D x ; map (x,y)->(eps^4 x, eps^6 y)
print("eps^4*d_main =", m(pw(eps,4),d_main), " (expect d_q up to sign)")
x0=(F(1641,8),F(-1160,8)); y0=(F(-123720,32),F(87483,32))
xs=m(pw(eps,4),x0); ys=m(pw(eps,6),y0)
print("image of P0:", xs, ys)
astar=(F(-1),F(7,4)); bstar=(F(39,8),F(-9,2)); cstar=m(astar,astar)
print("c* =",cstar, " a*b* =", m(astar,bstar))
print("P0 image == P* :", xs==cstar and ys==m(astar,bstar))
print("on quartic curve:", m(ys,ys)==sub(m(xs,m(xs,xs)),m(D,xs)))
print("b*^2 == c*^2 - D :", m(bstar,bstar)==sub(m(cstar,cstar),D))
print("N(c*+b*) =",N(a(cstar,bstar)), a(cstar,bstar), " N(c*-b*) =",N(sub(cstar,bstar)))
for v in [(F(3,4),F(1,2)),(F(-36,49),F(16,49))]:
    val=sub(a(m(D,m(v,v)),m((F(2),F(0)),m(bstar,v))),(F(1),F(0)))
    print("D v^2+2b* v-1 at",v,"=",val)
