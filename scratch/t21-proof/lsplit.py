# t21-proof: L(C_d,1) = theta-side + dual-side at split t (per-class formulas of Lcal.lean / HeckeFE).
import math, cmath
def unitOf(a,b):
    a%=4;b%=4
    if (a,b) in [(1,0),(3,2)]: return 1
    if (a,b) in [(3,0),(1,2)]: return -1
    if (a,b) in [(0,3),(2,1)]: return 1j
    if (a,b) in [(0,1),(2,3)]: return -1j
    return 0
def jacobi(a,n):
    # Jacobi symbol (a/n), n odd positive
    a%=n; r=1
    while a:
        while a%2==0:
            a//=2
            if n%8 in (3,5): r=-r
        a,n=n,a
        if a%4==3 and n%4==3: r=-r
        a%=n
    return r if n==1 else 0
def twChar(d,M,x1,x2):
    N=(x1%M)**2+(x2%M)**2
    if N%2==0: return 0
    return 0.25*jacobi(d,N)*unitOf(x1,x2)
def split(d,M,t,R=40):
    th=0
    for a1 in range(-R*M,R*M+1):
        for a2 in range(-R*M,R*M+1):
            n=a1*a1+a2*a2
            if n==0 or n> (R*R): continue
            c=twChar(d,M,a1,a2)
            if c==0: continue
            th+=c*complex(a1,a2)/n*math.exp(-math.pi*n*t/M**2)
    du=0
    cs=[(j1,j2,twChar(d,M,j1,j2)) for j1 in range(M) for j2 in range(M)]
    for b1 in range(-R,R+1):
        for b2 in range(-R,R+1):
            n=b1*b1+b2*b2
            if n==0 or n>R*R: continue
            D=0
            for (j1,j2,c) in cs:
                if c==0: continue
                a,b=j1/M,j2/M
                D+=c*(b1*math.sin(2*math.pi*a*b1)*math.cos(2*math.pi*b*b2)+1j*b2*math.cos(2*math.pi*a*b1)*math.sin(2*math.pi*b*b2))
            du+=D*math.exp(-math.pi*n/t)/n/M
    return th,du
for (d,M,t) in [(1,4,1),(1,4,4),(3,12,1),(3,12,12),(3,12,4)]:
    th,du=split(d,M,t,R=12 if M==12 else 20)
    print(d,M,t,"theta",th,"dual",du,"L",th+du)
