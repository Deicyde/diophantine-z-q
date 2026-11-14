from gsg_enum import mul, inv, nrd, form
from fractions import Fraction as Fr
import itertools, math
x4=(1,1,1,0); x6=(Fr(-3,2),0,Fr(1,2),0); mu=(0,0,2,1)
gens={'a':x4,'A':inv(x4),'b':x6,'B':inv(x6),'m':mu}
def word(w):
    r=(1,0,0,0)
    for ch in w: r=mul(r,gens[ch])
    return r
Gd=(-2,3,-6)
def cross(a,b): return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])
def dot(a,b): return sum(x*z for x,z in zip(a,b))
def q(s): return sum(Gd[k]*s[k]*s[k] for k in range(3))
def lin(u,base): return tuple(Gd[k]*(u[k+1]-base[k+1]) for k in range(3))
def analyze(base,nbrs,N):
    L=[lin(u,base) for u in nbrs]
    bvec=tuple(Gd[k]*base[k+1] for k in range(3))
    for a,b in itertools.combinations(range(len(L)),2):
        r=cross(L[a],L[b])
        for s in (r,tuple(-t for t in r)):
            if r!=(0,0,0) and all(dot(l,s)>=0 for l in L) and dot(bvec,s)>0:
                qs=q(s); ip=dot(bvec,s)
                print('  ray',a,b,[str(t) for t in s],'q',qs,'cosh^2=',ip*ip/(qs*N), float(ip*ip/(qs*N)))
for N,base,nb in ((3,(0,0,1,0),[(0,-3,3,-1),(0,-3,3,1),(0,0,3,-2),(0,0,3,2),(0,3,3,-1),(0,3,3,1)]),
                  (6,(0,0,2,1),[(0,Fr(-3,2),2,Fr(1,2)),(0,Fr(-3,2),4,Fr(5,2)),(0,Fr(3,2),2,Fr(1,2)),(0,Fr(3,2),4,Fr(5,2))])):
    print('N',N); analyze(base,nb,N)
# find word for the 4th N=6 neighbour
u=(0,Fr(-3,2),4,Fr(5,2))
for L in range(1,5):
    for w in itertools.product('aAbBm',repeat=L):
        s=word(w); t=mul(mul(inv(s),mu),s)
        if tuple(Fr(x) for x in t)==u: print('found',''.join(w)); break
    else: continue
    break
for N,base,pairs in ((3,(0,0,1,0),['abb','ABB','ab','AB','a','A']),(6,(0,0,2,1),['B','b','aBB'])):
    for w in pairs:
        s=word(w); print(N,w,[str(t) for t in s],'nrd',nrd(s),'inv',[str(t) for t in inv(s)])
