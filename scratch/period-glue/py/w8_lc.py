"""period-glue: polynomial identities for S8WeightExact on the generators g4 = 1+i+j, g6 = (j-3)/2 of Gamma*.
s = sqrt2, z = tau, W = a z + b, V = c z + d (g = iota(x) = [[a,b],[c,d]]).
 (I1) dFh(W,V) * (A Nf(z) + dF(z) B) = Nfh(W,V) * (C Nf(z) + dF(z) D)          (2x2 matrix identity)
 (I2) det(C Nf(z) + dF(z) D) * det g * (z-3)(z+1) = eps * dF(z)^2 * (W-3V)(W+V),  eps = -1
 (I3) M J M^T = J with Mathlib's J = [[0,-1],[1,0]]
Prints the quotients by s^2 - 2 (linear_combination coefficients, with sqrt2_sq : s*s = 2).
Run: ~/pyenv/bin/python -I w8_lc.py"""
import sympy as sp
s, z = sp.symbols('s z')
R_ = sp.Rational
def Nf(t):
    return sp.Matrix([[s*(t**2/2 + t - R_(3,2)) - t**2/2 - R_(3,2), s*(-t**2/2 - t + R_(3,2)) + t**2 + 3],
                      [s*(-t**2/2 - t + R_(3,2)) + t**2 + 3, s*(t**2 + 2*t - 3) - t**2 - 3]])
def Nfh(W, V):
    return sp.Matrix([[s*(W**2/2 + W*V - R_(3,2)*V**2) - W**2/2 - R_(3,2)*V**2, s*(-W**2/2 - W*V + R_(3,2)*V**2) + W**2 + 3*V**2],
                      [s*(-W**2/2 - W*V + R_(3,2)*V**2) + W**2 + 3*V**2, s*(W**2 + 2*W*V - 3*V**2) - W**2 - 3*V**2]])
def dF(t): return -s*(t-3)*(t+1)/2
def dFh(W, V): return -s*(W-3*V)*(W+V)/2
def iota(x):
    x0,x1,x2,x3 = x
    return sp.Matrix([[x0 + x1*s, -3*x2 - 3*s*x3], [x2 - s*x3, x0 - x1*s]])
gens = {"g4": ((1,1,1,0), sp.Matrix([[1,0,1,-2],[0,1,-2,2],[0,1,-1,2],[1,0,1,-1]]), -1, 2),
        "g6": ((R_(-3,2),0,R_(1,2),0), sp.Matrix([[0,0,0,-1],[0,0,1,0],[0,1,-1,2],[-1,0,-1,1]]), -1, 3)}
Jm = sp.Matrix([[0,0,-1,0],[0,0,0,-1],[1,0,0,0],[0,1,0,0]])
def red(e):
    q, r = sp.div(sp.Poly(sp.expand(e), s), sp.Poly(s**2 - 2, s))
    return sp.factor(q.as_expr()), sp.simplify(r.as_expr())
for name, (x, M, eps, detg) in gens.items():
    g = iota(x); a, b, c, d = g[0,0], g[0,1], g[1,0], g[1,1]
    W = a*z + b; V = c*z + d
    A, B, C, D = M[:2,:2], M[:2,2:], M[2:,:2], M[2:,2:]
    print(f"== {name}: x={x}, a={a}, b={b}, c={c}, d={d}, det g = {sp.expand(red(g.det())[1])} (expected {detg})")
    print("   M J M^T = J:", M*Jm*M.T == Jm, "  M^T J M = J:", M.T*Jm*M == Jm)
    L = dFh(W, V) * (A*Nf(z) + dF(z)*B); Rm = Nfh(W, V) * (C*Nf(z) + dF(z)*D)
    for i in range(2):
        for j in range(2):
            q, r = red(L[i,j] - Rm[i,j])
            print(f"   I1[{i},{j}] remainder {r}; coeff: {q}")
    P = C*Nf(z) + dF(z)*D
    q, r = red(P.det()*detg*(z-3)*(z+1) - eps*dF(z)**2*(W-3*V)*(W+V))
    print(f"   I2 remainder {r}; coeff: {q}")
