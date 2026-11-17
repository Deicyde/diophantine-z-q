"""Two-phase LP: (1) minimise the largest normalised row coefficient (log scale, primes 3 and 2);
(2) at that optimum + slack, minimise sum |exponents| so few coordinates move. Round to integers."""
import json, sys, math, re
from collections import Counter
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix, hstack, vstack, csr_matrix, identity
sys.path.insert(0, __file__.rsplit('/',1)[0])
from precise_lp import v
def build(data, fixed):
    E=int(re.fullmatch(r'3\^(\d+)',data['fixedParameter']['value'])[1])
    coords=data['coordinates']; rows=data['residuals']; n=len(coords); m=len(rows)
    idx={c['id']:i for i,c in enumerate(coords)}; L3,L2=math.log(3),math.log(2)
    N=2*n+2*m+1; nt=sum(len(r['terms']) for r in rows)
    A=lil_matrix((3*nt,N)); bb=np.zeros(3*nt); k=0
    for j,r in enumerate(rows):
        for t in r['terms']:
            c=Fraction(t['coefficient']); num,den=abs(c.numerator),c.denominator
            v3=v(3,num)-v(3,den); v2=v(2,num)-v(2,den)
            u=math.log(num)-math.log(den)-v3*L3-v2*L2
            e3c=v3+E*int(Fraction(t['sPower'])); cnt=Counter(t['monomial'])
            A[k,2*n+j]=1
            for i,mm in cnt.items(): A[k,idx[i]]-=mm
            bb[k]=e3c; k+=1
            A[k,2*n+m+j]=1
            for i,mm in cnt.items(): A[k,n+idx[i]]-=mm
            bb[k]=v2; k+=1
            for i,mm in cnt.items(): A[k,idx[i]]+=mm*L3; A[k,n+idx[i]]+=mm*L2
            A[k,2*n+j]-=L3; A[k,2*n+m+j]-=L2; A[k,N-1]=-1
            bb[k]=-u-e3c*L3-v2*L2; k+=1
    bounds=[(-60000,60000)]*N
    for c in coords:
        if c['name'] in fixed: bounds[idx[c['id']]]=(0,0); bounds[n+idx[c['id']]]=(0,0)
        if c['name'].startswith('OFFSET'): bounds[n+idx[c['id']]]=(0,0)
    return A.tocsr(),bb,bounds,n,m,N,idx
def solve(data, fixed=('input','inputProduct.quadratic'), slack=0.5, no2=False):
    A,bb,bounds,n,m,N,idx=build(data,fixed)
    if no2:
        for i in range(n,2*n): bounds[i]=(0,0)
    obj=np.zeros(N); obj[-1]=1
    r1=linprog(obj,A_ub=A,b_ub=bb,bounds=bounds,method='highs'); assert r1.success
    Z=r1.fun
    # phase 2: add p_i >= |a_i|, q_i>=|b_i| ; Z <= Z*+slack
    P=2*n
    A2=hstack([A,csr_matrix((A.shape[0],P))]).tolil()
    extra=lil_matrix((2*P+1,N+P)); be=np.zeros(2*P+1)
    for i in range(P):
        extra[2*i,i]=1; extra[2*i,N+i]=-1
        extra[2*i+1,i]=-1; extra[2*i+1,N+i]=-1
    extra[2*P,N-1]=1; be[2*P]=Z+slack
    AA=vstack([A2.tocsr(),extra.tocsr()]); BB=np.concatenate([bb,be])
    obj2=np.zeros(N+P); obj2[N:]=1
    r2=linprog(obj2,A_ub=AA,b_ub=BB,bounds=bounds+[(0,None)]*P,method='highs'); assert r2.success
    x=r2.x; coords=data['coordinates']
    pw={}
    for c in coords:
        a=round(x[idx[c['id']]]); b=round(x[n+idx[c['id']]])
        if a or b: pw[c['name']]=[a,b]
    return Z/math.log(10), pw
if __name__=='__main__':
    d=json.load(open(sys.argv[1])); slack=float(sys.argv[3]) if len(sys.argv)>3 else 0.5
    z,pw=solve(d,slack=slack)
    print('row log10 optimum %.2f -> poly ~%.1f digits; scaled coords %d'%(z,2*z,len(pw)))
    json.dump(pw,open(sys.argv[2],'w'),indent=1); print(json.dumps(pw))
