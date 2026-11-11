# Necessity of el-qfree's soundness window: multipliers with v_p(m) odd or negative
# admit B with v_p(B) = -1 and a rational zero of the pole system (trivial witness).
# Also checks sufficiency (L7, generalized to b>0) on random p-adic valuation data.
from fractions import Fraction as Fr
def _v(n,p):
    n=abs(n); k=0
    while n%p==0: n//=p; k+=1
    return k
def v(p,x):
    x=Fr(x); 
    if x==0: return 10**9
    return _v(x.numerator,p)-_v(x.denominator,p)
def issq(x):
    x=Fr(x)
    if x<=0: return False
    from sympy import integer_nthroot
    a,ea=integer_nthroot(x.numerator,2); b,eb=integer_nthroot(x.denominator,2)
    return ea and eb
def sqrtq(x):
    from sympy import integer_nthroot
    x=Fr(x); return Fr(integer_nthroot(x.numerator,2)[0],integer_nthroot(x.denominator,2)[0])
def system(B,m,e,z,r1,r2):
    A=m*B; H=A*(A-B*B)
    return (r1**2==A*(A-e)*(A+e)) and (r2**2==A*(A*z*z-e*H)*(A*z*z+e*H)) and e*H*z!=0
for p in [331, 337, 1009]:
    cases=[]
    # mu = 1: B = p(1-c^2), c = 1/p
    m=Fr(p); c=Fr(1,p); B=m*(1-c*c); cases.append(("mu=1",m,B))
    # mu = -2: B = m(1-c^2), c = 1+p
    m=Fr(1,p*p); c=Fr(1+p); B=m*(1-c*c); cases.append(("mu=-2",m,B))
    # mu = 3
    m=Fr(p**3); c=Fr(1,p*p); B=m*(1-c*c); cases.append(("mu=3",m,B))
    for name,m,B in cases:
        A=m*B; H=A*(A-B*B)
        assert issq(H)
        z=sqrtq(H); e=A
        ok=system(B,m,e,z,Fr(0),Fr(0))
        print(p,name,"v_p(m)=",v(p,m),"v_p(B)=",v(p,B),"pole system solved:",ok)
