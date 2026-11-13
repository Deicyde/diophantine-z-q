import sys, itertools, time
sys.path.insert(0,'scratch/igusa-generic')
from poly import *
Y=parse_defs('ZInQKernel/HDecomp/Textbook/Igusa/Generic.lean')
# normal form a = [s, r, q, p, 0, 1, 0] in variables (p,q,r,s)
def v4(i): e=[0]*4; e[i]=1; return {tuple(e):Fr(1)}
one={(0,0,0,0):Fr(1)}
A=[v4(3),v4(2),v4(1),v4(0),{},one,{}]
y=[[subst(Y[(n,k)],A) for k in range(3)] for n in range(1,4)]
print("y sizes", [[len(t) for t in r] for r in y])
w6=[60,-10,4,-3,4,-10,60]
def cub(u,v,t):
    return [ {k:val for k,val in __import__('functools').reduce(add,[mul(mul(u[i],v[j]),t[m-i-j]) for i in range(3) for j in range(3) if 0<=m-i-j<=2],{}).items()} for m in range(7)]
def p6(u,v):
    r={}
    for i in range(7): r=add(r, scal(Fr(w6[i]),mul(u[i],v[6-i])))
    return r
for t in itertools.combinations_with_replacement(range(3),3):
    t0=time.time()
    c=cub(y[t[0]],y[t[1]],y[t[2]])
    a=p6(A,c)
    print(t, len(a), max(sum(k) for k in a), "cub sizes", [len(x) for x in c], round(time.time()-t0,2))
