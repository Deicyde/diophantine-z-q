import sympy as sp
from gsg_sym import mul
n0,n1,n2,n3=sp.symbols('n0 n1 n2 n3')
R=sp.Rational
w=(n0+n2/R(2), n1+n3/R(2), n2/R(2), n3/R(2))
x4=(1,1,1,0); x4i=(R(1,2),R(-1,2),R(-1,2),0)
x6=(R(-3,2),0,R(1,2),0); x6i=(R(-1,2),0,R(-1,6),0)
def chk(x,z):
    for t in (mul(x,z),mul(z,x)): assert [sp.simplify(s) for s in t]==[1,0,0,0], t
def wit(x,z):
    A,B,C,D=[sp.expand(t) for t in mul(mul(x,w),z)]
    ms=[sp.expand(A-C),sp.expand(B-D),sp.expand(2*C),sp.expand(2*D)]
    ok=all(all(sp.Poly(m,n0,n1,n2,n3).coeff_monomial(v).is_integer for v in (n0,n1,n2,n3)) for m in ms)
    return ok,ms
for nm,(x,z) in {'x4':(x4,x4i),'x6':(x6,x6i)}.items():
    chk(x,z)
    print(nm,'x w z',wit(x,z)); print(nm,'z w x',wit(z,x))
a,b=sp.symbols('a b')
xx=(a,b,b,0); N=a**2+b**2; xb=(a,-b,-b,0)
u=[sp.factor(t/N) for t in mul(mul(xx,(0,0,1,0)),xb)]
print('u =',u)
