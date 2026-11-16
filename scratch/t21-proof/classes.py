# t21-proof: membership pattern of the 8 twoRep classes in D(1) = B^x H, H = Q^x U_3 (n = 3),
# via the invariant: beta_t in D(1) iff exists u in O_B^x with u*beta_t in Z + Z*omega_tau + 4 O_B.
# Quaternions as 4-tuples of Fractions (re, i, j, k).
from fractions import Fraction as F
from itertools import product
def mul(a,b):
    a0,a1,a2,a3=a; b0,b1,b2,b3=b
    return (a0*b0-a1*b1-a2*b2-a3*b3, a0*b1+a1*b0+a2*b3-a3*b2, a0*b2-a1*b3+a2*b0+a3*b1, a0*b3+a1*b2-a2*b1+a3*b0)
def hcoords(q):  # coords in basis 1,i,j,zeta, zeta=(-1+i+j+k)/2
    q0,q1,q2,q3=q
    return (q0+q3, q1-q3, q2-q3, 2*q3)
half=F(1,2)
units=[]
for s in product([-1,0,1],repeat=4):
    if sum(x*x for x in s)==1: units.append(tuple(F(x) for x in s))
for s in product([half,-half],repeat=4): units.append(s)
assert len(units)==24
def beta(t):
    a,b,c=t
    return (F(1-c),F(2*a+c),F(2*b+c),F(c))
def inR(q, om):  # q in Z + Z om + 4 O_B ?  q integral Hurwitz
    h=hcoords(q); ho=hcoords(om)
    for x in range(4):
        for y in range(4):
            d=[h[i]-x*(1 if i==0 else 0)-y*ho[i] for i in range(4)]
            if all(di.denominator==1 and di.numerator%4==0 for di in d): return (x,y)
    return None
for s in product([1,-1],repeat=3):
    om=(half,F(s[0],2),F(s[1],2),F(s[2],2))
    res={}
    for t in product([0,1],repeat=3):
        w=[(u,inR(mul(u,beta(t)),om)) for u in units]
        w=[(u,xy) for (u,xy) in w if xy is not None]
        res[t]=w[0] if w else None
    mem=[t for t in res if res[t]]
    print(s, "members:", mem, "witness:", {t:(res[t][0],res[t][1]) for t in mem if t!=(0,0,0)})
