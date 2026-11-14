import sympy as sp
from gsg_sym import mul
a,b,c,d=sp.symbols('a b c d')
x=(a,b,c,d); N=a**2-2*b**2+3*c**2-6*d**2
z=tuple(t/N for t in (a,-b,-c,-d))
R=sp.Rational
basis=[(1,0,0,0),(0,1,0,0),(R(1,2),0,R(1,2),0),(0,R(1,2),0,R(1,2))]
def coords(w): return [w[0]-w[2], w[1]-w[3], 2*w[2], 2*w[3]]
t=sum(coords(mul(mul(x,e),z))[k] for k,e in enumerate(basis))
print(sp.simplify(t - 4*a**2/N))
