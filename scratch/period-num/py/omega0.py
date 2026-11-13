import sympy as sp, mpmath as mp
mp.mp.dps=30
s2=sp.sqrt(2); I=sp.I
R=sp.Rational
basis=[(1,0,0,0),(0,1,0,0),(R(1,2),0,R(1,2),0),(0,R(1,2),0,R(1,2))]
Mi=sp.Matrix([[s2,0],[0,-s2]]); Mj=sp.Matrix([[0,-3],[1,0]])
def iota(x): return x[0]*sp.eye(2)+x[1]*Mi+x[2]*Mj+x[3]*Mi*Mj
tau=sp.symbols('tau'); v=sp.Matrix([tau,1])
cols=[iota(b)*v for b in basis]
Pinv=sp.Matrix([[-2,-1],[-1,-1]])
E=sp.Matrix.hstack(cols[0],cols[1]); F0=sp.Matrix.hstack(cols[2],cols[3])
Om=((F0*Pinv).inv()*E).applyfunc(sp.simplify)
print(Om)
O0=Om.subs(tau,s2+I).applyfunc(lambda e: sp.radsimp(sp.expand(sp.radsimp(e))))
print("Omega0=",O0)
for e in O0: print(sp.nsimplify(sp.re(sp.expand(e))), "|", sp.nsimplify(sp.im(sp.expand(e))), complex(e))
Y=O0.applyfunc(lambda e: sp.im(sp.expand(e)))
print("eig Y", [sp.N(x) for x in Y.eigenvals()])
