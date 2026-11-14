from gsg_enum import *
import itertools
pts=E(12)
def vec(v): return (v[1],v[2],v[3])
Gd=(-2,3,-6)
def lin(u): # functional v -> <v,u-y>
    w=[u[k]-y[k] for k in (1,2,3)]
    return tuple(Gd[k]*w[k] for k in range(3))
def cross(a,b): return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])
def dot(a,b): return sum(x*z for x,z in zip(a,b))
def q(s): return sum(Gd[k]*s[k]*s[k] for k in range(3))
def dirichlet(nbrs):
    L=[lin(u) for u in nbrs]
    rays=[]
    for a,b in itertools.combinations(range(len(L)),2):
        r=cross(L[a],L[b])
        if r==(0,0,0): continue
        for s in (r,tuple(-t for t in r)):
            if all(dot(l,s)>=0 for l in L):
                rays.append((a,b,s, q(s), dot(tuple(Gd[k]*s[k] for k in range(3)),vec(y))))
    return rays
for lim in (2,4,5,7):
    nb=[v for ip,v in pts if 1<ip<=lim]
    print('lim',lim,len(nb))
    for r in dirichlet(nb): print('  ',r[0],r[1],[str(t) for t in r[2]],'q=',r[3],'<s,y>=',r[4])
