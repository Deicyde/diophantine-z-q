# Exact check: Aut of the polarized QM surface (A, lambda) with End(A_Qbar) = O is {+-1}:
# u in O^* with u^dagger u = 1, u^dagger = mu^-1 ubar mu.  nrd(u)=1: u commutes with mu, u in Z[mu]^* = {+-1}.
# nrd(u)=-1: u = a i + b j + c ij pure, orthogonal to mu (b = c), u^2 = 1.  Search all u in O with
# coordinates in [-6,6] in the basis (1,i,(1+j)/2,(i+ij)/2) (u^dagger u = 1 forces nrd(u)^2 = 1; a box suffices as
# a sanity check; the exact argument is 2a^2+3b^2=1 with b in (1/2)Z, a in b+Z, which has no solution).
from fractions import Fraction as Fr
from itertools import product
import importlib.util, sys
H=Fr(1,2); A_,B_=2,-3
def mul(x,y):
    a1,b1,c1,d1=x; a2,b2,c2,d2=y
    return (a1*a2+A_*b1*b2+B_*c1*c2-A_*B_*d1*d2, a1*b2+b1*a2-B_*c1*d2+B_*d1*c2,
            a1*c2+c1*a2+A_*b1*d2-A_*d1*b2, a1*d2+d1*a2+b1*c2-c1*b2)
def conj(x): a,b,c,d=x; return (a,-b,-c,-d)
basis=[(1,0,0,0),(0,1,0,0),(H,0,H,0),(0,H,0,H)]
mu=(0,0,2,1); muinv=tuple(Fr(t,6) for t in conj(mu))
sols=[]
for co in product(range(-6,7),repeat=4):
    u=tuple(sum(c*b[k] for c,b in zip(co,basis)) for k in range(4))
    if mul(mul(mul(muinv,conj(u)),mu),u)==(1,0,0,0): sols.append(co)
print("u in box with mu^-1 ubar mu u = 1:", sols)
