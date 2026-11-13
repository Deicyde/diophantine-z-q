"""period-map: exact data for a Lean proof of OmegaSiegel. s stands for sqrt 2 (s^2 = 2), t for tau, x + i y = tau.
Prints: N = adj(F0*Pinv)*E reduced mod s^2-2 (entries linear in s), d = det(F0*Pinv), and for the imaginary parts
A_ij = Im(N_ij * conj d) (so Im Omega_ij = A_ij/|d|^2), the identities used in Lean with their quotients by s^2-2.
Run: ~/pyenv/bin/python -I omega_lean.py"""
import sympy as sp
s, t, x, y = sp.symbols('s t x y', real=True)
Mi = sp.Matrix([[s,0],[0,-s]]); Mj = sp.Matrix([[0,-3],[1,0]])
def iota(q): a,b,c,d = q; return a*sp.eye(2) + b*Mi + c*Mj + d*Mi*Mj
R = sp.Rational
basis = [(1,0,0,0),(0,1,0,0),(R(1,2),0,R(1,2),0),(0,R(1,2),0,R(1,2))]
v = sp.Matrix([t,1]); cols = [iota(b)*v for b in basis]
E = sp.Matrix.hstack(cols[0], cols[1]); F0 = sp.Matrix.hstack(cols[2], cols[3])
Pinv = sp.Matrix([[-2,-1],[-1,-1]])
F = F0*Pinv
def red(e): return sp.expand(sp.rem(sp.expand(e), s**2 - 2, s))
adj = sp.Matrix([[F[1,1], -F[0,1]], [-F[1,0], F[0,0]]])
N = (adj*E).applyfunc(red)
d = red(F.det())
print("d =", sp.factor(d))
for i in range(2):
    for j in range(2):
        print(f"N{i}{j} =", sp.collect(N[i,j], [s, t]))
print("N01 - N10 =", sp.expand(N[0,1]-N[1,0]))
# imaginary parts
tau = x + sp.I*y
def reim(e):
    e = sp.expand(e.subs(t, tau)); return sp.expand(sp.re(e)), sp.expand(sp.im(e))
dre, dim = reim(d)
A = {}
for i in range(2):
    for j in range(2):
        nre, nim = reim(N[i,j])
        A[(i,j)] = red(nim*dre - nre*dim)   # Im(N * conj d)
        print(f"A{i}{j} =", sp.factor(A[(i,j)]))
nd = red(dre**2 + dim**2); print("|d|^2 =", sp.factor(nd))
det = red(A[(0,0)]*A[(1,1)] - A[(0,1)]**2); print("A00*A11 - A01^2 =", sp.factor(det))
# --- quotients by s^2 - 2 for linear_combination in Lean
print("== quotients ==")
adjE = adj*E
def quo(e): q, r = sp.div(sp.expand(e), s**2 - 2, s); assert sp.expand(r) == 0, r; return sp.expand(q)
for i in range(2):
    for j in range(2):
        print(f"eN{i}{j} =", quo(adjE[i,j] - N[i,j]))
for i in range(2):
    for j in range(2):
        nre, nim = reim(N[i,j]); Aun = sp.expand(nim*dre - nre*dim)
        print(f"eA{i}{j} =", quo(Aun - A[(i,j)]))
print("eD =", quo(A[(0,0)]*A[(1,1)] - A[(0,1)]*A[(1,0)] - 3*y**2*(x**2 - 6*x + y**2 + 9)*(x**2 + 2*x + y**2 + 1)))
print("enormSq =", quo(dre**2 + dim**2 - (x**2 - 6*x + y**2 + 9)*(x**2 + 2*x + y**2 + 1)/2))
print("dre =", sp.factor(dre), " dim =", sp.factor(dim))
