# Check: q prod (1-q^{4n})^2 (1-q^{8n})^2 = sum_n heckeCoeff 1 n q^n, n <= 400.
# heckeCoeff 1 n = (1/4) sum_{a^2+b^2=n} unitOf(a,b mod 4) (a+bi)  (HeckeFE/Basic.lean:443,473).
N=400
P=[0]*(N+1); P[0]=1
def mulpoly(P,Q):
    R=[0]*(N+1)
    for i,x in enumerate(P):
        if x==0: continue
        for j,y in enumerate(Q):
            if i+j>N: break
            R[i+j]+=x*y
    return R
for n in range(1,N+1):
    for (k,e) in ((4,2),(8,2)):
        if k*n<=N:
            for _ in range(e):
                Q=[0]*(N+1); Q[0]=1; Q[k*n]=-1
                P=mulpoly(P,Q)
f=[0]+P[:N]   # times q
def unitOf(a,b):
    t=(a%4,b%4)
    if t in [(1,0),(3,2)]: return 1
    if t in [(3,0),(1,2)]: return -1
    if t in [(0,3),(2,1)]: return 1j
    if t in [(0,1),(2,3)]: return -1j
    return 0
import math
def hc(n):
    s=0
    r=int(math.isqrt(n))+1
    for a in range(-r,r+1):
        for b in range(-r,r+1):
            if a*a+b*b==n: s+=unitOf(a,b)*complex(a,b)
    return s/4
bad=[n for n in range(1,N+1) if abs(hc(n)-f[n])>1e-9]
print("mismatches up to",N,":",bad[:10], "count", len(bad))
print("first coeffs", f[1:30])
