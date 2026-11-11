# C3: the multiplier m = m0 k^2 with k RATIONAL gives explicit pole witnesses for every B.
# beta = sqf(m0 B), m0 B = beta g^2.  t(λ) = (1/(βλ) - λ)/2, k = g β t / m0.
# Then m(m-B) = (β²t⁴-1) v², v = k g / Y' (Y' = (1/(βλ)+λ)/2), since βY'² = 1+βt².
#   Loc β β   : torsion point (β,0) on C_β;
#   Loc (β·m(m-B)) β : x = β(βt²+1)² v² on C_{β(β²t⁴-1)v²}.
import random
from fractions import Fraction as F
from sympy import factorint, integer_nthroot
random.seed(1)
def sqf(x):
    x=F(x); n=x.numerator*x.denominator; s=-1 if n<0 else 1; r=1
    for p,e in factorint(abs(n)).items():
        if e%2: r*=p
    return s*r
def issq(x):
    x=F(x)
    return x>=0 and integer_nthroot(x.numerator,2)[1] and integer_nthroot(x.denominator,2)[1]
def sqrtq(x):
    return F(integer_nthroot(x.numerator,2)[0],integer_nthroot(x.denominator,2)[0])
def witnesses(B,m0,lam):
    beta=sqf(m0*B); g=sqrtq(m0*B/beta)
    t=(1/(beta*lam)-lam)/2; Yp=(1/(beta*lam)+lam)/2
    k=g*beta*t/m0; m=m0*k*k; th=m*(m-B)
    v=k*g/Yp
    assert th==(beta**2*t**4-1)*v*v
    d=beta*th; x=beta*(beta*t*t+1)**2*v*v
    ok1 = (beta**3-beta**2*beta)==0          # (β,0) on C_β
    ok2 = issq(x**3-d*d*x) and x!=0 and issq(x/beta)
    return beta,k,ok1 and ok2
# (a) 30 random B, m0 in {1,2,3,5,6,7}, random λ
okc=0
for i in range(30):
    B=F(random.randint(1,10**6),random.randint(1,10**3)**2)
    m0=random.choice([1,2,3,5,6,7]); lam=F(random.randint(1,50),random.randint(1,50))
    beta,k,ok=witnesses(B,m0,lam); okc+=ok
print("(a) explicit witnesses verified:",okc,"/30")
# (b) soundness side: B = c/p, v_p(B)=-1; v_p(k) over many λ
from sympy import primerange
def vp(x,p):
    x=F(x); 
    if x==0: return 99
    n,d=x.numerator,x.denominator; e=0
    while n%p==0: n//=p; e+=1
    while d%p==0: d//=p; e-=1
    return e
worst=-99
for p in [331,337,1009]:
    for c in [1,2,3,7]:
        B=F(c,p)
        for a in range(1,25):
            for b in range(1,25):
                for lam in [F(a,b),F(a,b*p),F(a*p,b),F(a,b*p*p)]:
                    beta,k,ok=witnesses(B,1,lam); assert ok
                    worst=max(worst,vp(k,p))
print("(b) B with v_p(B)=-1, p>324: max v_p(k) over λ samples =",worst,"(so v_p(m)<=-2: L7 boundary, Lemma 5.1 lost)")
# (c) instance-like B = b/δ² (δ with primes > 324, b with v_p(b) odd only at a few primes):
#     on this family k = G(ν²-βμ²)/(2 m0 δ μ ν), G = sqrt(m0 b/β); k ∈ Z[1/S] (S = primes <= 324)
#     forces μ | G, ν | Gβ (up to S-units) and ν² ≡ βμ² mod δ'. Enumerate all such λ = μ/ν.
from sympy import divisors, nextprime
Sset=set(primerange(2,325))
def Sint(x):
    d=F(x).denominator
    for p in factorint(d):
        if p not in Sset: return False
    return True
hits=0; tested=0
random.seed(7)
for i in range(30):
    P=[nextprime(random.randint(400,5000)) for _ in range(3)]
    b=P[0]*P[1]*random.choice([1,4,9,25])*7   # odd valuations at P0,P1,7 (contact-like)
    delta=P[2]*nextprime(random.randint(400,5000))
    B=F(b,delta**2); m0=random.choice([1,3,5,7])
    beta=sqf(m0*B); G=integer_nthroot((m0*b)//abs(beta),2)[0]
    assert G*G*abs(beta)==m0*b
    found=False
    for mu in divisors(G):
        for nu in divisors(G*abs(beta)):
            for s1 in [1,-1]:
                lam=F(s1*mu,nu); tested+=1
                if beta*lam*lam==1: continue
                bb,k,ok=witnesses(B,m0,lam); assert ok
                if Sint(k): found=True
    hits+=found
print("(c) instance-like B: S-integral k found on the family for",hits,"of 30 B (",tested,"λ tested)")
