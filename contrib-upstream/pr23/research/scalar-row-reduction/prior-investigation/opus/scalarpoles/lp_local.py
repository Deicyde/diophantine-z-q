from pathlib import Path
from collections import Counter
from fractions import Fraction
import json
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

import sys
data = json.loads(Path(sys.argv[1]).read_text())
coords, rows = data['coordinates'], data['residuals']
ids = {c['id']:i for i,c in enumerate(coords)}
n, m = len(coords), len(rows)
A = lil_matrix((sum(2*len(r['terms'])+1 for r in rows), n+2*m+1))
b = np.zeros(A.shape[0])
k=0
for j,row in enumerate(rows):
    lo, hi = n+2*j, n+2*j+1
    for t in row['terms']:
        for i,mult in Counter(t['monomial']).items():
            A[k, ids[i]]=mult
            A[k+1, ids[i]]=-mult
        A[k,hi]=-1
        A[k+1,lo]=1
        b[k]=-t['sPower']; b[k+1]=t['sPower']
        k+=2
    A[k,hi]=1; A[k,lo]=-1; A[k,-1]=-1
    k+=1
objective=np.zeros(A.shape[1]); objective[-1]=1
bounds=[(None,None)]*len(objective)
bounds[ids[0]]=(0,0); bounds[-1]=(0,None)
result=linprog(objective,A_ub=A.tocsr(),b_ub=b,bounds=bounds,method='highs')
print(result.message, 'optimum row spread', result.fun, flush=True)
if not result.success:
    raise RuntimeError(result.message)
weights={c['id']:Fraction(result.x[i]).limit_denominator(1000000) for i,c in enumerate(coords)}
spreads=[]
for row in rows:
    powers=[t['sPower']+sum(weights[i] for i in t['monomial']) for t in row['terms']]
    spreads.append((max(powers)-min(powers),row['name']))
print('Exact reconstructed maximum',max(spreads),flush=True)
chosen={c['name']:str(weights[c['id']]) for c in coords if weights[c['id']]}
Path(sys.argv[2]).write_text(json.dumps(chosen,indent=2)+'\n')
print(sorted(spreads,reverse=True)[:6])
