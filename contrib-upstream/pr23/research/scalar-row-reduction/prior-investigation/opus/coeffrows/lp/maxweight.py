import sys, json
from collections import Counter
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
def build(data, z, drop=()):
    coords, rows = data['coordinates'], data['residuals']
    rows=[r for r in rows if r['name'] not in drop]
    ids = {c['id']: i for i, c in enumerate(coords)}
    n, m = len(coords), len(rows)
    nt=sum(2*len(r['terms']) for r in rows)
    A = lil_matrix((nt, n+m)); b = np.zeros(nt); k=0
    # variable lo_j per row; constraint lo_j <= e_t <= lo_j + z
    for j,row in enumerate(rows):
        for t in row['terms']:
            s=float(Fraction(t['sPower']))
            for i,mult in Counter(t['monomial']).items():
                A[k,ids[i]]=-mult; A[k+1,ids[i]]=mult
            A[k,n+j]=1; b[k]=s       # lo - sum w <= s
            A[k+1,n+j]=-1; b[k+1]=z-s  # sum w - lo <= z - s
            k+=2
    return A.tocsr(), b, ids, n, m
def maxw(data, name, z, drop=(), sign=1):
    A,b,ids,n,m=build(data,z,drop)
    obj=np.zeros(n+m); i=next(ids[c['id']] for c in data['coordinates'] if c['name']==name); obj[i]=-sign
    bounds=[(None,None)]*(n+m); bounds[ids[0]]=(0,0)
    for i_ in range(n+m):
        if i_!=ids[0]: bounds[i_]=(-50,50)
    r=linprog(obj,A_ub=A,b_ub=b,bounds=bounds,method='highs')
    return (round(r.x[i],4), r.status) if r.success else r.message
if __name__=='__main__':
    d=json.load(open(sys.argv[1])); z=float(Fraction(sys.argv[2]))
    drop=('anchor.physicalA.definition','anchor.translatedEquation')
    for nm in sys.argv[3:]:
        print(nm, 'max', maxw(d,nm,z,drop), 'min', maxw(d,nm,z,drop,-1))
