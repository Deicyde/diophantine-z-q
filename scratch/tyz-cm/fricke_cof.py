import sympy as sp
a,b,p,r=sp.symbols('a b p r')
l=(2*b**2+p*r)/(b*(a-b))
x=2*a/b; xp=2+4*r/(p-r); yp=-4*(a**2-b**2)/(p-r)**2
D1=b**2*(a-b)**2*(p-r)
P1=sp.expand(sp.cancel((l**2-2-x-xp)*D1))
D2=b*(a-b)*(p-r)**2
P2=sp.expand(sp.cancel((-(l*(xp-2)-4)-yp)*D2))
G=[p**2-a**2-b**2, r**2-2*a*b]
for name,P in [('P1',P1),('P2',P2)]:
    Q,R=sp.reduced(P,G,p,r,a,b,order='lex')
    print(name,'=',P)
    print(' cof_p =',sp.factor(Q[0]))
    print(' cof_r =',sp.factor(Q[1]))
    print(' rem =',R)
# check l formula
y=-2*p*r/b**2
print(sp.simplify((-4+y)/(2-x)-l))
