"""period-map: Omega(tau) in closed form and Im Omega positive definite on H (sympy).
Omega = (F0 Pinv)^{-1} E as in pkg-I1. Run: ~/pyenv/bin/python -I omega_sym.py"""
import sympy as sp
t = sp.symbols('tau'); x, y = sp.symbols('x y', real=True)
s2 = sp.sqrt(2)
Mi = sp.Matrix([[s2,0],[0,-s2]]); Mj = sp.Matrix([[0,-3],[1,0]])
def iota(q): a,b,c,d = q; return a*sp.eye(2) + b*Mi + c*Mj + d*Mi*Mj
R = sp.Rational
basis = [(1,0,0,0),(0,1,0,0),(R(1,2),0,R(1,2),0),(0,R(1,2),0,R(1,2))]
v = sp.Matrix([t,1]); cols = [iota(b)*v for b in basis]
E = sp.Matrix.hstack(cols[0], cols[1]); F0 = sp.Matrix.hstack(cols[2], cols[3])
Pinv = sp.Matrix([[-2,-1],[-1,-1]])
Om = sp.simplify((F0*Pinv).inv()*E)
print("Omega =", Om)
print("symmetric:", sp.simplify(Om - Om.T) == sp.zeros(2))
Omxy = Om.subs(t, x + sp.I*y)
ImOm = sp.simplify(Omxy.applyfunc(lambda e: sp.im(sp.expand_complex(e))))
print("Im Omega =", ImOm)
print("det Im Omega =", sp.factor(sp.simplify(ImOm.det())))
print("Im Omega[0,0] =", sp.factor(ImOm[0,0])); print("Im Omega[1,1] =", sp.factor(ImOm[1,1]))
