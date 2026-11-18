# Check diophantine_zq.tex L412-418: the matrix of Trd(mu^{-1} x ybar), mu = 2j+ij, basis (1,i,(1+j)/2,(i+ij)/2).
from fractions import Fraction as F
T={(0,0):(1,0),(0,1):(1,1),(0,2):(1,2),(0,3):(1,3),(1,0):(1,1),(1,1):(2,0),(1,2):(1,3),(1,3):(2,2),
   (2,0):(1,2),(2,1):(-1,3),(2,2):(-3,0),(2,3):(3,1),(3,0):(1,3),(3,1):(-2,2),(3,2):(-3,1),(3,3):(6,0)}
def qm(a,b):
    r=[F(0)]*4
    for p in range(4):
        for q in range(4):
            c,ix=T[(p,q)]; r[ix]+=c*a[p]*b[q]
    return r
def conj(a): return [a[0],-a[1],-a[2],-a[3]]
def nrd(a): return a[0]**2-2*a[1]**2+3*a[2]**2-6*a[3]**2
def trd(a): return 2*a[0]
h=F(1,2)
basis=[[1,0,0,0],[0,1,0,0],[h,0,h,0],[0,h,0,h]]
mu=[F(0),F(0),F(2),F(1)]
n=nrd(mu); muinv=[x/n for x in conj(mu)]
assert qm(mu,muinv)==[1,0,0,0]
M=[[trd(qm(muinv,qm(x,conj(y)))) for y in basis] for x in basis]
print("nrd(mu) =",n," mu^2 =",qm(mu,mu))
for r in M: print([str(v) for v in r])
def det(m):
    m=[row[:] for row in m]; d=F(1); N=len(m)
    for c in range(N):
        p=next((r for r in range(c,N) if m[r][c]!=0),None)
        if p is None: return F(0)
        if p!=c: m[c],m[p]=m[p],m[c]; d=-d
        d*=m[c][c]
        for r in range(c+1,N):
            f=m[r][c]/m[c][c]; m[r]=[m[r][k]-f*m[c][k] for k in range(N)]
    return d
print("det =",det(M))
printed=[[0,0,-1,1],[0,0,1,-2],[1,-1,0,0],[-1,2,0,0]]
print("equals printed:",M==printed," equals minus printed:",M==[[-v for v in r] for r in printed])
