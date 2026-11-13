"""period-glue: emit the Lean lemmas I1/I2 for g4, g6 (coefficients from w8_lc.py's computation).
Run: ~/pyenv/bin/python -I w8_lean.py > w8_lean_out.txt"""
import sympy as sp
exec(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), 'w8_lc.py')).read().split("for name, (x, M, eps, detg) in gens.items():")[0])
def lean(e):
    t = sp.sstr(sp.expand(e)).replace('**', '^')
    return t.replace('s', 'S').replace('S', '(√2 : ℂ)')
def mat(Mx):
    return "!![" + "; ".join(", ".join(f"({lean(Mx[i,j])} : ℂ)" for j in range(2)) for i in range(2)) + "]"
for name, (x, M, eps, detg) in gens.items():
    g = iota(x); a, b, c, d = g[0,0], g[0,1], g[1,0], g[1,1]
    W = a*z + b; V = c*z + d
    A, B, C, D = M[:2,:2], M[:2,2:], M[2:,:2], M[2:,2:]
    L = dFh(W, V) * (A*Nf(z) + dF(z)*B); Rm = Nfh(W, V) * (C*Nf(z) + dF(z)*D)
    print(f"-- {name}: W = {lean(W)}, V = {lean(V)}")
    print(f"--   A = {mat(A)}  B = {mat(B)}  C = {mat(C)}  D = {mat(D)}")
    for i in range(2):
        for j in range(2):
            q, r = red(L[i,j] - Rm[i,j])
            print(f"--   I1[{i},{j}]: linear_combination ({lean(q)}) * sqrt2_sq")
    P = C*Nf(z) + dF(z)*D
    q, r = red(P.det()*detg*(z-3)*(z+1) - eps*dF(z)**2*(W-3*V)*(W+V))
    print(f"--   I2: linear_combination ({lean(q)}) * sqrt2_sq")
