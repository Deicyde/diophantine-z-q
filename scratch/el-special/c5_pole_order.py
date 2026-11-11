# C5: check Lemma G Cor. 2: along n = c + λ, q = q0 λ^{-M}, fixed tests D_j ∈ ℚ(√2),
# the test-site pole input B = R/Θ² has v_p(B) = 15 - 52M at λ = p (p large).
from fractions import Fraction as F
import random
random.seed(3)
C=[0,-15,-20,-24,-30,-60]
class K:  # a + b√2
    def __init__(s,a,b=0): s.a=F(a); s.b=F(b)
    def __add__(s,o): o=o if isinstance(o,K) else K(o); return K(s.a+o.a,s.b+o.b)
    def __mul__(s,o): o=o if isinstance(o,K) else K(o); return K(s.a*o.a+2*s.b*o.b,s.a*o.b+s.b*o.a)
    def inv(s): n=s.a*s.a-2*s.b*s.b; return K(s.a/n,-s.b/n)
def vp(x,p):
    x=F(x); n,d=x.numerator,x.denominator; e=0
    while n%p==0: n//=p; e+=1
    while d%p==0: d//=p; e-=1
    return e
for p in [1000003, 998244353]:
  for c in [0,-24]:
    for M in [1,2,3]:
        lam=F(p); n=c+lam; Fn=F(1)
        for cc in C: Fn*=(n-cc)
        R0=F(2730)**6*abs(Fn); q=F(random.randint(1,99),random.randint(1,99))/lam**M
        a0=1-R0*q*q; R=R0*a0*a0
        D=[K(random.randint(1,50),random.randint(1,50)) for _ in range(6)]
        W=K(1)
        for d in D:
            Cj=d*K(1/Fn); W=W*(K(1)+Cj*Cj*K(R))
        Theta=2*W.inv().a
        B=R/Theta**2
        print(p,c,M,"v_p(B) =",vp(B,p),"predicted",15-52*M)
