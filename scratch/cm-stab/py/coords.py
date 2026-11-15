from fractions import Fraction as F
import itertools
def qmul(x,y):
    a1,b1,c1,d1=x; a2,b2,c2,d2=y
    # basis 1,i,j,k ; i^2=2, j^2=-3, k=ij, k^2=6, ik=2j, ki=-2j, jk=3i, kj=-3i, ji=-k
    re = a1*a2 + 2*b1*b2 - 3*c1*c2 + 6*d1*d2
    i_ = a1*b2 + b1*a2 + (c1*d2)*3 + (d1*c2)*(-3)
    j_ = a1*c2 + c1*a2 + (b1*d2)*2 + (d1*b2)*(-2)
    k_ = a1*d2 + d1*a2 + b1*c2 - c1*b2
    return (re,i_,j_,k_)
def ofInt(n): return (n[0]+F(n[2],2), n[1]+F(n[3],2), F(n[2],2), F(n[3],2))
def toInt(x):
    n2=2*x[2]; n3=2*x[3]; n0=x[0]-x[2]; n1=x[1]-x[3]
    return (n0,n1,n2,n3)
def mulCoord(n,m):
    return [m[0]*n[0]+2*m[1]*n[1]+2*m[1]*n[3]-m[2]*n[2]+2*m[3]*n[3],
     m[0]*n[1]+m[1]*n[0]+m[1]*n[2]-m[2]*n[3]+m[3]*n[2],
     m[0]*n[2]-2*m[1]*n[3]+m[2]*n[0]+m[2]*n[2]+2*m[3]*n[1],
     m[0]*n[3]-m[1]*n[2]+m[2]*n[1]+m[2]*n[3]+m[3]*n[0]]
import random
# check mulCoord = product
for _ in range(100):
    n=[random.randint(-5,5) for _ in range(4)]; m=[random.randint(-5,5) for _ in range(4)]
    assert toInt(qmul(ofInt(n),ofInt(m)))==tuple(mulCoord(n,m)), (n,m)
print("mulCoord ok: ofInt n * ofInt m = ofInt (mulCoord n m)")
jc=(-1,0,2,0); kc=(0,-1,0,2)
print("j=",ofInt(jc),"k=",ofInt(kc))
E=[(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)]
def lin(f):
    cols=[toInt(f(ofInt(e))) for e in E]
    return [[cols[c][r] for c in range(4)] for r in range(4)]
aj=lambda x: tuple(F(-1,3)*t for t in qmul(qmul(ofInt(jc),x),ofInt(jc)))
ak=lambda x: tuple(F(1,6)*t for t in qmul(qmul(ofInt(kc),x),ofInt(kc)))
print("alpha_j matrix", lin(aj))
print("alpha_k matrix", lin(ak))
# red: (n0-n2, n1-n3) mod 3 gaussian
def red(n): return ((n[0]-n[2])%3,(n[1]-n[3])%3)
def gm(a,b): return ((a[0]*b[0]-a[1]*b[1])%3,(a[0]*b[1]+a[1]*b[0])%3)
for n in itertools.product(range(3),repeat=4):
  for m in itertools.product(range(3),repeat=4):
    assert red(mulCoord(n,m))==gm(red(n),red(m))
print("red multiplicative mod 3")
# conj
for n in itertools.product(range(3),repeat=4):
    r=red(n); a=toInt(aj(ofInt(n))); b=toInt(ak(ofInt(n)))
    assert red(a)==(r[0],(-r[1])%3), (n,a)
    assert red(b)==(r[0],(-r[1])%3), (n,b)
print("red alpha = conj")
# j^{-1} y in O iff mulCoord(jc,n)= 0 mod 3 ; j z coords
print("j*ofInt n coords:", [[mulCoord(jc,e)[r] for e in E] for r in range(4)])
print("ofInt n*j coords:", [[mulCoord(e,jc)[r] for e in E] for r in range(4)])
print("k*ofInt n coords:", [[mulCoord(kc,e)[r] for e in E] for r in range(4)])
# y*y=-3 => mulCoord(jc,y)=0 mod 3 ; check over residues: y*y = 0 mod 3
for n in itertools.product(range(3),repeat=4):
    if all(t%3==0 for t in mulCoord(n,n)):
        assert all(t%3==0 for t in mulCoord(jc,n)), n
        assert red(n)==(0,0)
print("y^2=0 mod 3 => j y = 0 mod3 and red y = 0")
for n in itertools.product(range(2),repeat=4):
    if all(t%2==0 for t in mulCoord(n,n)):
        assert all(t%2==0 for t in mulCoord(kc,n)), n
for n in itertools.product(range(3),repeat=4):
    if all(t%3==0 for t in mulCoord(n,n)):
        assert all(t%3==0 for t in mulCoord(kc,n)), n
print("y^2=0 mod 2,3 => k y = 0 mod 2,3")
