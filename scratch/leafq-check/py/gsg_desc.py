import sympy as sp
from gsg_sym import mul
R=sp.Rational
b,c,d=sp.symbols('b c d')
v=(0,b,c,d)
x4=(1,1,1,0); x4i=(R(1,2),R(-1,2),R(-1,2),0)
x6=(R(-3,2),0,R(1,2),0); x6i=(R(-1,2),0,R(-1,6),0)
pairs=[(x6,x6i),(x6i,x6),(mul(x6,x4),mul(x4i,x6i)),(mul(x6i,x4i),mul(x4,x6))]
for s,si in pairs:
    print([sp.nsimplify(t) for t in s],[sp.nsimplify(t) for t in si], [sp.simplify(t) for t in mul(s,si)])
    w=mul(mul(s,v),si)
    print('  pairY =',sp.expand(-2*w[1]+3*w[2]),' minus pairY v:',sp.expand(-2*w[1]+3*w[2]-(-2*b+3*c)))
print(sp.expand(3*(-2*b**2+3*c**2-6*d**2)-(-2*b+3*c)**2 - ((b+3*d)*(-5*b+6*c-3*d)+(b-3*d)*(-5*b+6*c+3*d))))
