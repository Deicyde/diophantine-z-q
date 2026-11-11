"""Check of the upstream ADVERSE-CASE claims about the bielliptic pair on y^2 = f(x^2) (generic cubic f).
(1) sigma1:(x,y)->(-x,y), sigma2:(x,y)->(-x,-y) = sigma1*iota; quotients E1: v^2=f(U) via (U,v)=(x^2,y),
    E2: w^2=U f(U) via (U,w)=(x^2,x*y). Points a=(s,0), b=(-s,0) with f(s^2)=0 have equal images under both.
(2) The pair (a,b) with f1(a)=f1(b), f2(a)=f2(b), a!=b forces sigma1(a)=sigma2(a), i.e. iota(a)=a (Weierstrass).
(3) Degree of phi = (f1_*, f2_*): phi phi^dagger = diag([2],[2]) on E1 x E2 (STANDARD: f_*f^* = [deg f], and the
    off-diagonal terms vanish), deg [2] on an elliptic curve is 4, so deg(phi)^2 = 16 and deg phi = 4."""
from sympy import symbols, expand, simplify
x, y, s, a0, a1, a2, a3 = symbols('x y s a0 a1 a2 a3')
f = lambda U: a3*U**3 + a2*U**2 + a1*U + a0
f1 = lambda P: (P[0]**2, P[1])
f2 = lambda P: (P[0]**2, P[0]*P[1])
A, B = (s, 0), (-s, 0)
print("f1(a)==f1(b):", f1(A) == f1(B), " f2(a)==f2(b):", f2(A) == f2(B), " a!=b (s!=0):", A != B)
# images lie on the quotient curves given f(s^2)=0:
print("E1 eq at image:", simplify(f1(A)[1]**2 - f(f1(A)[0]) + f(s**2)))   # = 0 when f(s^2)=0
print("E2 eq at image:", simplify(f2(A)[1]**2 - f2(A)[0]*f(f2(A)[0]) + s**2*f(s**2)))
# (2): general point P=(x,y); fibres of f1: {P, sigma1 P}; of f2: {P, sigma2 P}; intersection beyond P needs sigma1 P = sigma2 P
s1 = (-x, y); s2 = (-x, -y)
print("sigma1 P == sigma2 P iff y == 0:", [simplify(u - v) for u, v in zip(s1, s2)])
print("deg diag([2],[2]) =", 4*4, "=> deg phi =", int((4*4)**0.5))
