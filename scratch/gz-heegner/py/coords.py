from sympy import symbols, expand, simplify, factor, Rational, sqrt, together, cancel
A,B,a,k,l,Cp,s = symbols('A B a k l Cp s')
C = a*Cp - B*k - A*k**2
D = B**2 - 4*A*C
Bp = B + 2*A*k
b = 2*a*l - Bp
c0 = cancel((b**2 - D)/(4*a))
print("c0 =", expand(c0))
tau = (-B + s)/(2*A)
taup = (-Bp + s)/(2*a*A)
wJ = (-b + s)/2
def red(e):
    # reduce polynomial in s modulo s^2 = D
    e = expand(e)
    from sympy import Poly
    P = Poly(e, s)
    out = 0
    for (deg,), c in P.terms():
        out += c * (D**(deg//2)) * s**(deg % 2)
    return expand(out)
def coords(e):
    # e = x + y*tau
    e = red(e)
    y = cancel(e.coeff(s) * 2*A)
    x = cancel(e - y*tau).subs(s, 0)
    x = cancel(expand(e - y*tau))
    return factor(x), factor(y)
for name, e in [("a*taup", a*taup), ("wJ", wJ), ("wJ*taup", wJ*taup)]:
    print(name, coords(e))
