import json,sys,math,copy
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import vstack, csr_matrix
sys.path.insert(0,'lp'); sys.path.insert(0,'measure')
import variants as V
from offsets import add_offsets
from weights import build
H=json.load(open('runs/vA/final/integer-candidate-ir.json'))
CH=[('scalar.chain3.definition','scalar.shiftedS.f.1'),('scalar.chain2.definition','scalar.shiftedS.f.0')]
V.d0=H
for nm,d in [('B',add_offsets(H,CH)),('C',add_offsets(V.fanchor(2),CH))]:
    A,bb,bounds,n,m,N,idx=build(d,('input','inputProduct.quadratic'))
    obj=np.zeros(N); obj[-1]=1
    r=linprog(obj,A_ub=A,b_ub=bb,bounds=bounds,method='highs'); Z=r.fun
    offs=[idx[c['id']] for c in d['coordinates'] if c['name'].startswith('OFFSET')]
    for slack in [0.5, 5, 20]:
        bnd=list(bounds); bnd[-1]=(None,Z+slack*math.log(10)/2)
        out=[]
        for i in offs:
            for s in (1,-1):
                o=np.zeros(N); o[i]=s
                rr=linprog(o,A_ub=A,b_ub=bb,bounds=bnd,method='highs'); out.append(round(rr.x[i]))
        # also sum k3+k2 / differences
        print(nm,'slack(poly digits)',slack,'k3 range',out[1],out[0],'k2 range',out[3],out[2])

print('--- fixing k3, k2 to S multiples')
for nm,d in [('B',add_offsets(H,CH)),('C',add_offsets(V.fanchor(2),CH))]:
    A,bb,bounds,n,m,N,idx=build(d,('input','inputProduct.quadratic'))
    offs=[idx[c['id']] for c in d['coordinates'] if c['name'].startswith('OFFSET')]
    for k3 in [-2130,-4260]:
        for k2 in [-2130,-4260,None]:
            bnd=list(bounds); bnd[offs[0]]=(k3,k3)
            if k2 is not None: bnd[offs[1]]=(k2,k2)
            obj=np.zeros(N); obj[-1]=1
            r=linprog(obj,A_ub=A,b_ub=bb,bounds=bnd,method='highs')
            print(nm,k3,k2,'digits~%.1f'%(2*r.fun/math.log(10)), 'k2=',round(r.x[offs[1]]))

print('--- bounded constant offsets |k|<=K')
for nm,d in [('B',add_offsets(H,CH)),('C',add_offsets(V.fanchor(2),CH))]:
    A,bb,bounds,n,m,N,idx=build(d,('input','inputProduct.quadratic'))
    offs=[idx[c['id']] for c in d['coordinates'] if c['name'].startswith('OFFSET')]
    for K in [600,1000,1340]:
        bnd=list(bounds); bnd[offs[0]]=(-K,K); bnd[offs[1]]=(-K,K)
        obj=np.zeros(N); obj[-1]=1
        r=linprog(obj,A_ub=A,b_ub=bb,bounds=bnd,method='highs')
        print(nm,K,'digits~%.1f'%(2*r.fun/math.log(10)), [round(r.x[o]) for o in offs])
