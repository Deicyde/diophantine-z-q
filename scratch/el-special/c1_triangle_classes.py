# C1: (a) explicit points of C_N for N = b(a-b)a(a+b) (three-term AP a-b,a,a+b with difference b)
#     and their abscissa classes; (b) the abscissa-class group they generate; (c) whether
#     a fixed squarefree beta with omega(beta)>=3 can be such a class with (a-b),a,(a+b) prime.
from fractions import Fraction as F
from sympy import factorint, isprime
def sqf(x):
    x=F(x); n=x.numerator*x.denominator; s=-1 if n<0 else 1; r=1
    for p,e in factorint(abs(n)).items():
        if e%2: r*=p
    return s*r
def on_curve(x,N):
    v=x**3-N*N*x
    if v<0: return False
    from sympy import integer_nthroot
    a,b=v.numerator,v.denominator
    return integer_nthroot(a,2)[1] and integer_nthroot(b,2)[1]
ok=0; tot=0; classes_seen=set()
for a in range(2,40):
    for b in range(1,a):
        from math import gcd
        if gcd(a,b)!=1: continue
        N=b*(a-b)*a*(a+b)
        pts=[F(N*a,b),F(-N*b,a),F(N*(a+b),(a-b)),F(-N*(a-b),(a+b))]
        for x in pts:
            tot+=1; ok+=on_curve(x,F(N))
        cl=sorted({sqf(x) for x in pts})
        exp=sorted({sqf(a*a-b*b),sqf(-(a*a-b*b)),sqf(a*b),sqf(-a*b)})
        assert cl==exp,(a,b,cl,exp)
print("points on curve:",ok,"/",tot)
# (c) AP-prime configurations: classes available are +-(a^2-b^2)=+-(a-b)(a+b) [two primes] and +-ab.
cnt=0
for a in range(3,2000):
    for b in range(2,a,2):
        if isprime(a-b) and isprime(a) and isprime(a+b):
            cnt+=1
            c1=abs(sqf((a-b)*(a+b))); c2=abs(sqf(a*b))
            # omega of the class that contains two of the AP primes is exactly 2 (+ primes of b in the ab class)
            assert len(factorint(c1))==2
print("prime 3-APs tested:",cnt,"; class (a^2-b^2) always has exactly two prime factors")
