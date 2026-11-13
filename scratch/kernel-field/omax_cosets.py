from fractions import Fraction as F
from itertools import product
# B=(2,-3): i^2=2, j^2=-3, k=ij, k^2=6. x=(a,b,c,d) = a+bi+cj+dk
def mul(x,y):
    a1,b1,c1,d1=x; a2,b2,c2,d2=y
    # general (alpha,beta)=(2,-3)
    al,be=2,-3
    return (a1*a2+al*b1*b2+be*c1*c2-al*be*d1*d2,
            a1*b2+b1*a2-be*c1*d2+be*d1*c2,
            a1*c2+c1*a2+al*b1*d2-al*d1*b2,
            a1*d2+d1*a2+b1*c2-c1*b2)
def trd(x): return 2*x[0]
def nrd(x): a,b,c,d=x; return a*a-2*b*b+3*c*c-6*d*d
def ofInt(n): return (n[0]+F(n[2],2), n[1]+F(n[3],2), F(n[2],2), F(n[3],2))
basis=[ofInt(v) for v in [(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)]]
# check i*i
print(mul((0,1,0,0),(0,1,0,0)), mul((0,0,1,0),(0,0,1,0)), mul((0,0,0,1),(0,0,0,1)))
# O closed under mult?
import itertools
def inO(x):
    a,b,c,d=x
    n2=2*c; n3=2*d; n0=a-c; n1=b-d
    return all(F(v).denominator==1 for v in (n2,n3,n0,n1))
print(all(inO(mul(u,v)) for u in basis for v in basis))
# dual: x with trd(x*e) in Z for e in basis. Solve: trace form matrix
import sympy as sp
M=sp.Matrix(4,4,lambda r,s: trd(mul(basis[r],basis[s])))
print(M, M.det())
Minv=M.inv()
# dual basis e*_s = sum_r Minv[r,s] e_r  (in coordinates of 1,i,j,k)
def comb(coeffs):
    res=[F(0)]*4
    for cf,e in zip(coeffs,basis):
        for t in range(4): res[t]+=F(int(sp.fraction(cf)[0]),int(sp.fraction(cf)[1]))*e[t]
    return tuple(res)
dual=[comb([Minv[r,s] for r in range(4)]) for s in range(4)]
print(dual)
# enumerate cosets: x = sum t_s dual_s, t mod (index). index = det=36? enumerate t in range(0,12)^4 and dedupe mod O
seen={}
good=[]
for t in product(range(12),repeat=4):
    x=tuple(sum(F(t[s])*dual[s][q] for s in range(4)) for q in range(4))
    # reduce mod O: coordinates n
    a,b,c,d=x
    key=(F(2*c)%1, F(2*d)%1, F(a-c)%1, F(b-d)%1)
    if key in seen: continue
    seen[key]=x
    if F(nrd(x)).denominator==1: good.append(x)
print(len(seen), good)
