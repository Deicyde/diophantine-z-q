# Certificates A*F + B*G = r0*x^7 and A'*F + B'*G = r0*y^7 for the binary forms
# F_h = x(x+15y)(x+20y)(x+24y)(x+30y)(x+60y), G_h = 7x^2+300xy+3600y^2 (deg A = 1, deg B = 5).
from sympy import symbols, expand, Poly, resultant, solve, factorint, Rational
x, y = symbols('x y')
F = x*(x+15*y)*(x+20*y)*(x+24*y)*(x+30*y)*(x+60*y)
G = 7*x**2 + 300*x*y + 3600*y**2
r0 = resultant(F.subs(y, 1), G.subs(y, 1), x)
print("Res(F,G) =", r0, factorint(r0))
def cert(target):
    a = symbols('a0:2'); b = symbols('b0:6')
    A = sum(a[i]*x**(1-i)*y**i for i in range(2))
    B = sum(b[i]*x**(5-i)*y**i for i in range(6))
    eqs = Poly(expand(A*F + B*G - target), x, y).coeffs()
    s = solve(eqs, list(a)+list(b), dict=True)[0]
    return expand(A.subs(s)), expand(B.subs(s))
for t in (x**7, y**7):
    A, B = cert(t)
    print("target", t); print("  A =", A); print("  B =", B)
    assert expand(A*F + B*G - t) == 0
    from sympy import lcm, fraction, Poly as P
    den = 1
    for c in P(A, x, y).coeffs() + P(B, x, y).coeffs():
        den = lcm(den, fraction(c)[1])
    print("  common denominator =", den, factorint(den))
    l1 = sum(abs(c) for c in P(expand(den*A), x, y).coeffs()) + sum(abs(c) for c in P(expand(den*B), x, y).coeffs())
    print("  l1 of den*(A,B) =", l1)
