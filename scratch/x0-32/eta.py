import itertools, math
from fractions import Fraction
N=32; DIVS=[1,2,4,8,16,32]; PREC=80
def mul(a,b):
    c=[0]*PREC
    for i,x in enumerate(a):
        if x:
            for j in range(PREC-i):
                c[i+j]+=x*b[j]
    return c
def inv(a):
    # a[0]=1
    b=[0]*PREC; b[0]=Fraction(1,a[0])
    for n in range(1,PREC):
        b[n]=-sum(a[k]*b[n-k] for k in range(1,n+1))/a[0]
    return b
def etaprod(d):
    s=[0]*PREC; s[0]=1
    for n in range(1,PREC//d+1):
        f=[0]*PREC; f[0]=1
        if d*n<PREC: f[d*n]=-1
        s=mul(s,f)
    return s
E={d:etaprod(d) for d in DIVS}
Einv={d:inv(E[d]) for d in DIVS}
def quot(r):
    s=[0]*PREC; s[0]=1
    for d,e in zip(DIVS,r):
        for _ in range(abs(e)):
            s=mul(s,E[d] if e>0 else Einv[d])
    return s  # times q^{sum d r_d/24}
def order_at(r,c):
    # order at cusp with denominator c (in local parameter), Ligozat
    g=math.gcd(c,N//c)
    return Fraction(N,24)*sum(math.gcd(c,d)**2*e/Fraction(g*c*d) for d,e in zip(DIVS,r))
def ok(r):
    if sum(r)!=0: return False
    if sum(d*e for d,e in zip(DIVS,r))%24: return False
    if sum((N//d)*e for d,e in zip(DIVS,r))%24: return False
    p=1
    for d,e in zip(DIVS,r): p*=Fraction(d)**e
    sq=math.isqrt(p.numerator)**2==p.numerator and math.isqrt(p.denominator)**2==p.denominator
    return sq
res=[]
R=range(-6,7)
for r in itertools.product(R,repeat=6):
    if not ok(r): continue
    o={c:order_at(r,c) for c in DIVS}
    # pole only at infinity (c=32)
    if all(o[c]>=0 for c in DIVS if c!=32) and o[32] in (-2,-3,-1):
        res.append((r,o[32],sum(abs(e) for e in r)))
res.sort(key=lambda t:t[2])
for t in res[:40]: print(t)
