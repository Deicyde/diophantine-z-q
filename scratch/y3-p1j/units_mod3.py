# O = Z<1,i,(1+j)/2,(i+ij)/2> in B=(2,-3|Q) (i^2=2, j^2=-3, ij=-ji=k). Count (O/3O)^*, norms mod 3.
from fractions import Fraction as F
import itertools, random
T={(0,0):(1,0),(0,1):(1,1),(0,2):(1,2),(0,3):(1,3),(1,0):(1,1),(1,1):(2,0),(1,2):(1,3),(1,3):(2,2),
   (2,0):(1,2),(2,1):(-1,3),(2,2):(-3,0),(2,3):(3,1),(3,0):(1,3),(3,1):(-2,2),(3,2):(-3,1),(3,3):(6,0)}
def qm(a,b):
    r=[F(0)]*4
    for p in range(4):
        for q in range(4):
            c,ix=T[(p,q)]; r[ix]+=c*a[p]*b[q]
    return r
for _ in range(200):
    x,y,z=[[random.randint(-3,3) for _ in range(4)] for _ in range(3)]
    assert qm(qm(x,y),z)==qm(x,qm(y,z))
h=F(1,2)
basis=[[1,0,0,0],[0,1,0,0],[h,0,h,0],[0,h,0,h]]
def elt(c): return [sum(c[m]*basis[m][r] for m in range(4)) for r in range(4)]
def coords(v):  # invert: v = a*1 + b*i + c*(1+j)/2 + d*(i+k)/2
    c=2*v[2]; d=2*v[3]; a=v[0]-c/2; b=v[1]-d/2; return [a,b,c,d]
def nrd(v): a,b,c,d=v; return a*a-2*b*b+3*c*c-6*d*d
for x in basis:
    for y in basis:
        assert all(t.denominator==1 for t in coords(qm(x,y)))
els=list(itertools.product(range(3),repeat=4))
def mulmod(x,y): return tuple(int(t)%3 for t in coords(qm(elt(x),elt(y))))
one=(1,0,0,0)
units=[x for x in els if any(mulmod(x,y)==one and mulmod(y,x)==one for y in els)]
n1=[x for x in units if int(nrd(elt(x)))%3==1]
print("|O/3O| =",len(els),"; |(O/3O)^*| =",len(units),"; norm 1 mod 3:",len(n1),"; norm -1 mod 3:",len(units)-len(n1))
print("manuscript bound 4|(O/3O)^*| =",4*len(units),"<= 4*81 = 324:",4*len(units)<=324)
print("|N/(A_f^* K_3)| = 4|(O/3O)^*|/|(Z/3)^*| =",4*len(units)//2)
