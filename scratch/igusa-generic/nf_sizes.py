import sympy as sp, itertools, sys
sys.path.insert(0,'/tmp/t28')
x,z=sp.symbols('x z')
def tv(phi, psi, k):
    m = sp.Poly(phi, x, z).total_degree(); n = sp.Poly(psi, x, z).total_degree()
    s = 0
    for j in range(k + 1):
        s += (-1)**j * sp.binomial(k, j) * sp.diff(phi, x, k - j, z, j) * sp.diff(psi, x, j, z, k - j)
    return sp.expand(sp.factorial(m - k) * sp.factorial(n - k) / (sp.factorial(m) * sp.factorial(n)) * s)
p,q,r,s=sp.symbols('p q r s')
c=[s,r,q,p,0,1,0]
f=sp.expand(sum(ci*x**i*z**(6-i) for i,ci in enumerate(c)))
i=tv(f,f,4); y1=tv(f,i,4); y2=tv(i,y1,2); y3=tv(i,y2,2)
for nm,y in [('y1',y1),('y2',y2),('y3',y3)]:
    P=sp.Poly(y,x,z)
    print(nm,[len(sp.Poly(P.coeff_monomial(x**k*z**(2-k)),p,q,r,s).terms()) if P.coeff_monomial(x**k*z**(2-k))!=0 else 0 for k in range(3)])
ys=[y1,y2,y3]
for t in [(0,0,0),(2,2,2)]:
    a=tv(f,sp.expand(ys[t[0]]*ys[t[1]]*ys[t[2]]),6)
    print(t,len(sp.Poly(a,p,q,r,s).terms()))
