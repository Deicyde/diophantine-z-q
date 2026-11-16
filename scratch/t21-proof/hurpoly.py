# Hurwitz-coordinate product formula: y = hur(x) = x0 + x1 i + x2 j + x3 zeta, zeta = (-1+i+j+k)/2.
from fractions import Fraction as F
from itertools import product
# polynomials: dict monomial(tuple of exponents over 8 vars) -> coeff
def padd(a,b):
    r=dict(a)
    for k,v in b.items(): r[k]=r.get(k,0)+v
    return {k:v for k,v in r.items() if v!=0}
def pmul(a,b):
    r={}
    for k1,v1 in a.items():
        for k2,v2 in b.items():
            k=tuple(x+y for x,y in zip(k1,k2)); r[k]=r.get(k,0)+v1*v2
    return {k:v for k,v in r.items() if v!=0}
def var(i):
    e=[0]*8; e[i]=1; return {tuple(e):F(1)}
def const(c): return {tuple([0]*8):F(c)} if c else {}
def sc(c,a): return {k:v*c for k,v in a.items() if v*c!=0}
def hur(xs):  # returns (re,i,j,k)
    x0,x1,x2,x3=xs
    h=F(1,2)
    return (padd(x0,sc(-h,x3)), padd(x1,sc(h,x3)), padd(x2,sc(h,x3)), sc(h,x3))
def qmul(a,b):
    a0,a1,a2,a3=a; b0,b1,b2,b3=b
    s=lambda *ps: ps
    re=padd(padd(pmul(a0,b0),sc(-1,pmul(a1,b1))),padd(sc(-1,pmul(a2,b2)),sc(-1,pmul(a3,b3))))
    i=padd(padd(pmul(a0,b1),pmul(a1,b0)),padd(pmul(a2,b3),sc(-1,pmul(a3,b2))))
    j=padd(padd(pmul(a0,b2),sc(-1,pmul(a1,b3))),padd(pmul(a2,b0),pmul(a3,b1)))
    k=padd(padd(pmul(a0,b3),pmul(a1,b2)),padd(sc(-1,pmul(a2,b1)),pmul(a3,b0)))
    return (re,i,j,k)
def hc(q):
    q0,q1,q2,q3=q
    return (padd(q0,q3), padd(q1,sc(-1,q3)), padd(q2,sc(-1,q3)), sc(2,q3))
X=[var(i) for i in range(4)]; Y=[var(4+i) for i in range(4)]
names=['a0','a1','a2','a3','b0','b1','b2','b3']
def show(p):
    terms=[]
    for k,v in sorted(p.items()):
        mon='*'.join(names[i] if e==1 else f'{names[i]}^{e}' for i,e in enumerate(k) if e)
        assert v.denominator==1, (k,v)
        terms.append(f'({v.numerator})*{mon}' if mon else f'({v.numerator})')
    return ' + '.join(terms) if terms else '0'
P=hc(qmul(hur(X),hur(Y)))
for i in range(4): print(f'c{i} =', show(P[i]))
# star
S=hc((hur(X)[0], sc(-1,hur(X)[1]), sc(-1,hur(X)[2]), sc(-1,hur(X)[3])))
for i in range(4): print(f'star{i} =', show(S[i]))
# nrd
h=hur(X); N=padd(padd(pmul(h[0],h[0]),pmul(h[1],h[1])),padd(pmul(h[2],h[2]),pmul(h[3],h[3])))
print('nrd =', show(N))
