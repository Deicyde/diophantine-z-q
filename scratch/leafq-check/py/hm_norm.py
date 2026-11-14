import sympy as sp
from gsg_sym import mul
n0,n1,n2,n3=sp.symbols('n0 n1 n2 n3')
R=sp.Rational
w=(n0+n2/R(2), n1+n3/R(2), n2/R(2), n3/R(2))
mu=(0,0,2,1); mui=(0,0,R(-1,3),R(-1,6))
assert [sp.simplify(t) for t in mul(mu,mui)]==[1,0,0,0]
def wit(x,z):
    A,B,C,D=[sp.expand(t) for t in mul(mul(x,w),z)]
    ms=[sp.expand(A-C),sp.expand(B-D),sp.expand(2*C),sp.expand(2*D)]
    ok=all(all(sp.Poly(m,n0,n1,n2,n3).coeff_monomial(v).is_integer for v in (n0,n1,n2,n3)) for m in ms)
    return ok,ms
print(wit(mu,mui)); print(wit(mui,mu))
