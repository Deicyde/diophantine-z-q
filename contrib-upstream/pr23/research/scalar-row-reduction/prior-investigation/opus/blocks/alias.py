import sys,random
from sample import *
d=load(sys.argv[1]); S=pow(3,2130,P)
ids=[c['id'] for c in d['coordinates']]; nm={c['id']:c['name'] for c in d['coordinates']}
N=len(ids)+25
random.seed(1)
rows=[]
for k in range(N):
    val,_=sample(d,S); rows.append([1]+[val[i] for i in ids])
# kernel of rows (N x M): find vectors v with rows*v=0. Row reduce.
M=len(ids)+1
A=[r[:] for r in rows]; piv=[]; r=0
for c in range(M):
    p=None
    for i in range(r,len(A)):
        if A[i][c]: p=i;break
    if p is None: continue
    A[r],A[p]=A[p],A[r]; inv=pow(A[r][c],P-2,P); A[r]=[x*inv%P for x in A[r]]
    for i in range(len(A)):
        if i!=r and A[i][c]:
            f=A[i][c]; A[i]=[(x-f*y)%P for x,y in zip(A[i],A[r])]
    piv.append(c); r+=1
free=[c for c in range(M) if c not in piv]
print('rank',r,'of',M,'free cols',len(free))
cols=['1']+[nm[i] for i in ids]
for f in free:
    rel={cols[f]:1}
    for i,pc in enumerate(piv):
        if A[i][f]: rel[cols[pc]]=(-A[i][f])%P
    def show(x): return x if x<P//2 else x-P
    print('RELATION:', {k:show(v) for k,v in rel.items()})
