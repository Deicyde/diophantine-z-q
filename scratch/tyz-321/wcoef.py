"""tyz-321: integer coefficients for the lattice identities of the w-action (n = 8k+5):
 b*<1,t2> = <c, c*tau>,  b*<1/32,t2> = <c/32, c*tau>,
 b = <m, -4+4w>, m = (n+1)/2, t2 = (-(n+2)+w)/(8(n+4)), c = (-1+((n+3)/2)w)/(n+4), tau = (1+w)/(4(n+1))."""
from fractions import Fraction as Fr
import itertools
def mul(x,y,n): return (x[0]*y[0]-n*x[1]*y[1], x[0]*y[1]+x[1]*y[0])
def data(k, N=1):
    n = 8*k+5; m = (n+1)//2
    h0 = (Fr(m),Fr(0)); h1 = (Fr(-4),Fr(4))
    t2 = (Fr(-(n+2),8*(n+4)), Fr(1,8*(n+4)))
    c = (Fr(-1,n+4), Fr((n+3)//2, n+4))
    tau = (Fr(1,4*(n+1)), Fr(1,4*(n+1)))
    one = (Fr(1,N),Fr(0))
    S=[h0,h1]; T=[one,t2]
    B=[mul(c,one,n), mul(c,tau,n)]
    return n,S,T,B
def solve2(B, x):
    # x = p B0 + q B1
    a,b = B[0]; c,d = B[1]
    det = a*d-b*c
    p = (x[0]*d - x[1]*c)/det; q = (a*x[1]-b*x[0])/det
    return p,q
def interp(vals):  # vals at k=0..3 -> check quadratic in k with integer coefficients
    # fit a + b k + c k^2 using k=0,1,2, verify k=3
    a = vals[0]; c = (vals[2]-2*vals[1]+vals[0])/2; b = vals[1]-a-c
    ok = all(a+b*k+c*k*k == vals[k] for k in range(len(vals)))
    return (a,b,c) if ok else None
for N in (1, 32):
    print("N =",N)
    # subset: products s*t in span(B)
    for i,j in itertools.product(range(2),range(2)):
        ps=[];qs=[]
        for k in range(6):
            n,S,T,B = data(k,N)
            p,q = solve2(B, mul(S[i],T[j],n)); ps.append(p); qs.append(q)
        print(" s%d*t%d ="%(i,j), interp(ps), interp(qs), "integral:", all(x.denominator==1 for x in ps+qs))
    # superset: find pair of products forming basis
    for (i1,j1),(i2,j2) in itertools.combinations(list(itertools.product(range(2),range(2))),2):
        good=True; rows=[]
        for k in range(6):
            n,S,T,B = data(k,N)
            P=[mul(S[i1],T[j1],n), mul(S[i2],T[j2],n)]
            co=[]
            for b in B:
                p,q = solve2(P,b); co += [p,q]
            if not all(x.denominator==1 for x in co): good=False;break
            rows.append(co)
        if good:
            print(" basis pair", (i1,j1),(i2,j2), [interp([r[t] for r in rows]) for t in range(4)])

# verification of the explicit coefficients used in L321.lean
def chk(k):
    for N in (1,32):
        n,S,T,B = data(k,N)
        h0,h1 = S; t0,t2 = T
        P = lambda s,t: mul(s,t,n)
        comb = lambda a,b,c_,d: tuple(a*P(h0,t0)[i]+b*P(h0,t2)[i]+c_*P(h1,t0)[i]+d*P(h1,t2)[i] for i in range(2))
        if N == 1:
            bp = 11-484*k+21296*k*k; gp = -(1-44*k+1936*k*k+2662*k**3)
            assert comb(0,0,0,-1) == B[0]
            assert comb(0,bp,gp,8*gp) == B[1]
        else:
            assert comb(1,3*(k+1),-4*(k+1)*(3*k+2),-(k+1)*(3*k+2)) == B[0]
            assert comb(0,3,-12*k-8,-3*k-2) == B[1]
    return True
print(all(chk(k) for k in range(40)))
