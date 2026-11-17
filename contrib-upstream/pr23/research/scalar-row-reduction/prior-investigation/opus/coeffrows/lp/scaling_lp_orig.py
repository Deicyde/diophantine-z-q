from pathlib import Path
from collections import Counter
from fractions import Fraction
import json
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

ROOT = Path('/tmp/codex-glazer389-review-3j08z564/cube')
data = json.loads((ROOT/'build/final380/final/integer-candidate-ir.json').read_text())
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
Path('/tmp/quartic-after13/scaling_weights.json').write_text(json.dumps(chosen,indent=2)+'\n')
np.savez('/tmp/quartic-after13/scaling_solver.npz', x=result.x, dual=result.ineqlin.marginals)
print('Nonzero weights',len(chosen),'tight rows',sum(s==max(spreads)[0] for s,_ in spreads),flush=True)
dual=[Fraction(y).limit_denominator(1000000) for y in result.ineqlin.marginals]
assert all(y<=0 for y in dual)
certificate=[Fraction(0)]*len(objective)
matrix=A.tocsr()
for j,y in enumerate(dual):
    if y:
        for at in range(matrix.indptr[j],matrix.indptr[j+1]):
            certificate[matrix.indices[at]]+=y*int(matrix.data[at])
assert all(v==0 for j,v in enumerate(certificate[:-1]) if j!=ids[0])
assert certificate[-1]==1
lower=sum(y*int(v) for y,v in zip(dual,b))
assert lower==Fraction(1,3)
Path('/tmp/quartic-after13/scaling_dual.json').write_text(json.dumps({'rowSpreadLowerBound':str(lower),'fixedInputCoefficient':str(certificate[ids[0]]),'nonzeroDualMultipliers':{str(i):str(y) for i,y in enumerate(dual) if y},'scope':'Exact certificate for powers-of-S diagonal scalings of these fixed residual rows; not global circuit optimality.'},indent=2)+'\n')
print('Exact dual certificate: lower bound',lower,'with',sum(bool(y) for y in dual),'nonzero multipliers',flush=True)
