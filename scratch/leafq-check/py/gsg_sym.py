import sympy as sp
a,b,c,d=sp.symbols('a b c d')
def mul(x,y):
    a1,b1,c1,d1=x; a2,b2,c2,d2=y
    A,Bq=2,-3
    return (a1*a2 + A*b1*b2 + Bq*c1*c2 - A*Bq*d1*d2,
            a1*b2 + b1*a2 - Bq*c1*d2 + Bq*d1*c2,
            a1*c2 + c1*a2 + A*b1*d2 - A*d1*b2,
            a1*d2 + d1*a2 + b1*c2 - c1*b2)
x=(a,b,c,d); xb=(a,-b,-c,-d); y=(0,1,1,0)
N=a**2-2*b**2+3*c**2-6*d**2
v=mul(mul(x,y),xb)
print([sp.expand(t) for t in v])
pv=sp.expand(-2*v[1]+3*v[2])
print('pairY(x y xbar) - N =',sp.factor(pv-N))
# try SOS: it's a quadratic form; matrix
M=sp.hessian(pv-N,(a,b,c,d))/2
print(M, M.eigenvals())
comm=[sp.expand(s-t) for s,t in zip(mul(x,y),mul(y,x))]
print('xy-yx',comm)
