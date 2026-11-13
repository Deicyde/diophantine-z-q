"""Check covariance of Lean's yv: yv(actC f a b c d e) i = e^{3,5,7} det^{8,14,20} qAct(yv f i) a b c d
on random rational inputs (exact). Run: python3 -I scratch/igusa-generic/cov_check.py (repo root)"""
import random, sys
sys.path.insert(0,'scratch/igusa-generic')
from poly import *
Y=parse_defs('ZInQKernel/HDecomp/Textbook/Igusa/Generic.lean')
print({k:len(v) for k,v in Y.items()})
from math import comb
def actC(f,a,b,c,d,e):
    # e * sum f_k (a x + b)^k (c x + d)^(6-k), coefficients in x
    res=[Fr(0)]*7
    for k in range(7):
        # (ax+b)^k
        p1=[comb(k,j)*Fr(a)**j*Fr(b)**(k-j) for j in range(k+1)]
        p2=[comb(6-k,j)*Fr(c)**j*Fr(d)**(6-k-j) for j in range(7-k)]
        for i,u in enumerate(p1):
            for j,v in enumerate(p2): res[i+j]+=e*f[k]*u*v
    return res
def qAct(q,a,b,c,d):
    return [q[0]*d**2+q[1]*b*d+q[2]*b**2, 2*q[0]*c*d+q[1]*(a*d+b*c)+2*q[2]*a*b, q[0]*c**2+q[1]*a*c+q[2]*a**2]
def yv(f): return [[ev(Y[(n,k)],f) for k in range(3)] for n in range(1,4)]
random.seed(1)
for trial in range(5):
    f=[Fr(random.randint(-5,5)) for _ in range(7)]
    a,b,c,d,e=[Fr(random.randint(-4,4)) for _ in range(5)]
    dt=a*d-b*c
    if dt==0 or e==0: continue
    L=yv(actC(f,a,b,c,d,e)); R=yv(f)
    for n,(dg,w) in enumerate([(3,8),(5,14),(7,20)]):
        rhs=[e**dg*dt**w*t for t in qAct(R[n],a,b,c,d)]
        assert L[n]==rhs, (trial,n)
print("covariance OK")
