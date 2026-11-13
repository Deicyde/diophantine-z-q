"""period-num: exact data for the proof of NormalizerDecomp (part_normalizer.lean). Pure python3, Fractions.
oBasis = (1, i, (1+j)/2, (i+ij)/2); coordinates n of a = sum n_k oB_k: n = (a0-a2, a1-a3, 2a2, 2a3)."""
from fractions import Fraction as Fr
from weight_check import qmul, nrd, conj, inv, trd, oB, sc
def coords(a): a0,a1,a2,a3=a; return [a0-a2, a1-a3, 2*a2, 2*a3]
def lmat(c):  # matrix of a -> c*a in oBasis coords (columns = images of oB_k)
    cols=[coords(qmul(c,b)) for b in oB]; return [[cols[k][l] for k in range(4)] for l in range(4)]
def rmat(c):
    cols=[coords(qmul(b,c)) for b in oB]; return [[cols[k][l] for k in range(4)] for l in range(4)]
def show(M): return [[str(t) for t in row] for row in M]
iinv=inv((0,1,0,0)); p3=(0,0,1,1); p3inv=inv(p3)
print("i^-1 =",iinv," pi3^-1 =",p3inv, " i*pi3 =",qmul((0,1,0,0),p3), " pi3^2 =",qmul(p3,p3))
print("left mult by i^-1, oBasis coords:",show(lmat(iinv)))
print("left mult by pi3^-1:",show(lmat(p3inv)))
# w z w^-1 for w = i, pi3 (needed for normalizing in the other direction)
for name,w in [("i",(0,1,0,0)),("pi3",p3)]:
    M=[[None]*4 for _ in range(4)]
    for k,b in enumerate(oB):
        c=coords(qmul(qmul(w,b),inv(w)))
        for l in range(4): M[l][k]=c[l]
    print(f"b -> {name} b {name}^-1 :",show(M))
# dual basis w.r.t. trd(ab)
import itertools
T=[[trd(qmul(a,b)) for b in oB] for a in oB]
print("trace form matrix:",show(T))
# invert T (4x4) with Fractions
def minv(M):
    n=len(M); A=[list(map(Fr,row))+[Fr(int(i==j)) for j in range(n)] for i,row in enumerate(M)]
    for c in range(n):
        p=next(r for r in range(c,n) if A[r][c]!=0); A[c],A[p]=A[p],A[c]
        pv=A[c][c]; A[c]=[t/pv for t in A[c]]
        for r in range(n):
            if r!=c and A[r][c]!=0:
                f=A[r][c]; A[r]=[a-f*b for a,b in zip(A[r],A[c])]
    return [row[n:] for row in A]
Ti=minv(T)
# dual basis: e_k^# = sum_l Ti[l][k] oB_l  so that trd(oB_m e_k^#) = delta
dual=[tuple(sum(Ti[l][k]*oB[l][c] for l in range(4)) for c in range(4)) for k in range(4)]
for k in range(4):
    print(f"dual_{k} =",tuple(str(t) for t in dual[k]),"  6*dual coords:",[str(t) for t in coords(sc(6,dual[k]))])
for m in range(4):
    assert all(trd(qmul(oB[m],dual[k]))==(1 if m==k else 0) for k in range(4))
# Casimir: sum_k oB_k a dual_k = trd(a) on basis elements
for a in [(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)]:
    s=[0,0,0,0]
    for k in range(4):
        t=qmul(qmul(oB[k],a),dual[k]); s=[x+y for x,y in zip(s,t)]
    print("Casimir on",a,":",[str(t) for t in s]," trd =",trd(a))
