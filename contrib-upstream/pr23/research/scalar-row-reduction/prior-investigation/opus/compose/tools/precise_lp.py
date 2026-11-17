"""LP on log of normalized row coefficients with separate exponents of 3 and 2.
Minimizes max_r [max_t log|coef_t| - log(content-ish)], row content approximated by 2^min*3^min."""
import json, sys, math, re
from collections import Counter
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
def v(p,x):
    k=0
    while x%p==0: x//=p; k+=1
    return k
def solve(data, fix=('input',), fix2=None):
    E=int(re.fullmatch(r'3\^(\d+)',data['fixedParameter']['value'])[1])
    coords=data['coordinates']; rows=data['residuals']; n=len(coords)
    idx={c['id']:i for i,c in enumerate(coords)}
    m=len(rows); L3,L2=math.log(3),math.log(2)
    # vars: a(n), b(n), lo3(m), lo2(m), Z
    N=2*n+2*m+1
    nt=sum(len(r['terms']) for r in rows)
    A=lil_matrix((3*nt,N)); bb=np.zeros(3*nt); k=0
    for j,r in enumerate(rows):
        # common denominator handling: coefficients are rational
        for t in r['terms']:
            c=Fraction(t['coefficient']); num,den=abs(c.numerator),c.denominator
            v3=v(3,num)-v(3,den); v2=v(2,num)-v(2,den)
            u=math.log(num)-math.log(den)-v3*L3-v2*L2
            e3c=v3+E*int(Fraction(t['sPower']))
            cnt=Counter(t['monomial'])
            # lo3_j - e3_t <= 0
            A[k,2*n+j]=1
            for i,mm in cnt.items(): A[k,idx[i]]-=mm
            bb[k]=e3c; k+=1
            A[k,2*n+m+j]=1
            for i,mm in cnt.items(): A[k,n+idx[i]]-=mm
            bb[k]=v2; k+=1
            # u + (e3-lo3)L3 + (e2-lo2)L2 <= Z
            for i,mm in cnt.items(): A[k,idx[i]]+=mm*L3; A[k,n+idx[i]]+=mm*L2
            A[k,2*n+j]-=L3; A[k,2*n+m+j]-=L2; A[k,N-1]=-1
            bb[k]=-u-e3c*L3-v2*L2; k+=1
    obj=np.zeros(N); obj[-1]=1
    bounds=[(-60000,60000)]*N
    for c in coords:
        if c['name'] in fix: bounds[idx[c['id']]]=(0,0); bounds[n+idx[c['id']]]=(0,0)
        if c['name'].startswith('OFFSET') or (fix2 and c['name'] in fix2): bounds[n+idx[c['id']]]=(0,0)
    res=linprog(obj,A_ub=A.tocsr(),b_ub=bb,bounds=bounds,method='highs')
    assert res.success,res.message
    a={c['name']:res.x[idx[c['id']]] for c in coords}; b={c['name']:res.x[n+idx[c['id']]] for c in coords}
    return res.fun, a, b
if __name__=='__main__':
    d=json.load(open(sys.argv[1]))
    Z,a,b=solve(d)
    print('LP row log10 max', Z/math.log(10), ' => poly digits ~', 2*Z/math.log(10))
    pw={k:[round(a[k]),round(b[k])] for k in a if round(a[k]) or round(b[k])}
    json.dump(pw,open(sys.argv[2],'w'),indent=1)
    print(len(pw),'scaled coords')
