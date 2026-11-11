# rv-h-trust: J(u) = -57600 F^2 / G^6 never takes a branch value 0, oo, -16/27 at rational u not in C.
import sympy as sp
u=sp.symbols('u')
F=u*(u+15)*(u+20)*(u+24)*(u+30)*(u+60); G=7*u**2+300*u+3600
H=(u**2-60*u-1800)*(13*u**2+480*u+3600)*(11*u**2+600*u+7200)
print("G^6-97200F^2 == H^2:", sp.expand(G**6-97200*F**2-H**2)==0)
J=-57600*F**2/G**6
num=sp.factor(sp.together(J+sp.Rational(16,27)))
print("J+16/27 =", num)
for q in [u**2-60*u-1800,13*u**2+480*u+3600,11*u**2+600*u+7200,G]:
    d=sp.discriminant(q,u); print(q, "disc", d, "square?", sp.sqrt(d).is_rational)
