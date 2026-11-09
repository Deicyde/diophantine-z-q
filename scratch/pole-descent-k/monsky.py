"""Explicit 2-descent for congruent number curves C_n: y^2 = x^3 - n^2 x, n odd squarefree.
Normalized Selmer representatives (a,b) = (x, x-n) classes with a,b positive odd divisors of n;
odd-prime conditions give the matrix M_n = [[A, D_{-1}],[D_2, A + D_{-1}]]; the 2-adic condition
is checked separately with the table of the 2-adic image."""
import itertools
def leg(a, p):  # additive Legendre symbol: 0 if a is a nonzero square mod p, 1 if nonsquare
    a %= p
    assert a
    return 0 if pow(a, (p - 1) // 2, p) == 1 else 1

def primes_of(n):
    ps=[];d=2;m=n
    while d*d<=m:
        if m%d==0:
            ps.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: ps.append(m)
    return ps

def img2_ok(a, b, n):
    """(a,b) positive odd: is (a,b) in the 2-adic image of C_n (n odd)?"""
    a8, b8, n8 = a % 8, b % 8, n % 8
    # image tables (pairs of unit classes mod 8 with b-valuation 0), from img2.py
    T = {1: {(1,1),(1,5),(7,3),(7,7)}, 7: {(1,1),(1,5),(7,1),(7,5)},
         3: {(1,1),(1,5),(7,1),(7,5)}, 5: {(1,1),(1,5),(7,3),(7,7)}}
    return (a8, b8) in T[n8]

def matrix(ps):
    k=len(ps)
    A=[[0]*k for _ in range(k)]
    for i,p in enumerate(ps):
        for j,q in enumerate(ps):
            if i!=j: A[i][j]=leg(q,p)
        A[i][i]=sum(A[i][j] for j in range(k) if j!=i)%2
    Dm=[leg(-1,p) for p in ps]; D2=[leg(2,p) for p in ps]
    M=[]
    for i in range(k):
        M.append([A[i][j] for j in range(k)]+[Dm[i] if j==i else 0 for j in range(k)])
    for i in range(k):
        M.append([D2[i] if j==i else 0 for j in range(k)]+[(A[i][j]+(Dm[i] if j==i else 0))%2 for j in range(k)])
    return M

def kernel(M, ncols):
    rows=[sum(b<<j for j,b in enumerate(r)) for r in M]
    piv={}
    for r in rows:
        for c in sorted(piv,reverse=True):
            if r>>c&1: r^=piv[c]
        if r:
            c=r.bit_length()-1
            for c2 in list(piv):
                if piv[c2]>>c&1: piv[c2]^=r
            piv[c]=r
    free=[j for j in range(ncols) if j not in piv]
    ker=[]
    for f in free:
        v=1<<f
        for c,r in piv.items():
            if r>>f&1: v|=1<<c
        ker.append(v)
    return ker

def selmer_reps(n):
    """All normalized Selmer reps (a,b) (including (1,1)) -> list; dim Sel_2 = 2 + log2(len)."""
    ps=primes_of(n); k=len(ps)
    ker=kernel(matrix(ps),2*k)
    out=[]
    for coeffs in itertools.product([0,1],repeat=len(ker)):
        v=0
        for c,w in zip(coeffs,ker):
            if c: v^=w
        a=1;b=1
        for i,p in enumerate(ps):
            if v>>i&1: a*=p
            if v>>(k+i)&1: b*=p
        out.append((a,b,img2_ok(a,b,n)))
    return out

if __name__=="__main__":
    import sys
    for n in map(int,sys.argv[1:]):
        r=selmer_reps(n)
        print(n,len(r),sum(t for *_,t in r),r)
