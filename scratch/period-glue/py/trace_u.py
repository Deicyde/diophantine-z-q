# Check: for B = (2,-3) (i^2=2, j^2=-3, k=ij), u2(w) = -3*(2w + i w p) + j*(2w + i w p)*q satisfies
# re(u2(1)) + imI(u2(i)) + imJ(u2(j)) + imK(u2(k)) = -24 identically in p, q (trace of w -> u2(w)).
import sympy as sp
c1, c2 = 2, -3
def mul(x, y):
    a1,b1,c_1,d1 = x; a2,b2,c_2,d2 = y
    # QuaternionAlgebra R c1 0 c2 (Mathlib 3-param with c2=0): i^2=c1, j^2=c3, k=ij, k^2=-c1 c3
    return (a1*a2 + c1*b1*b2 + c2*c_1*c_2 - c1*c2*d1*d2,
            a1*b2 + b1*a2 - c2*c_1*d2 + c2*d1*c_2,
            a1*c_2 + c_1*a2 + c1*b1*d2 - c1*d1*b2,
            a1*d2 + d1*a2 + b1*c_2 - c_1*b2)
P = sp.symbols('p0:4'); Q = sp.symbols('q0:4')
I = (0,1,0,0); J = (0,0,1,0)
def add(x,y): return tuple(a+b for a,b in zip(x,y))
def sm(s,x): return tuple(s*a for a in x)
def u2(w):
    u1 = add(sm(2,w), mul(mul(I,w),P))
    return add(sm(-3,u1), mul(mul(J,u1),Q))
basis = [(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)]
tr = sum(sp.expand(u2(basis[k])[k]) for k in range(4))
print("trace =", sp.simplify(tr))
# sanity: i*j and k
print("i*i", mul(I,I), "j*j", mul(J,J), "i*j", mul(I,J), "j*i", mul(J,I))
