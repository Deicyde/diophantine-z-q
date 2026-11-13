from fractions import Fraction as F
def J4f(u, v): return -128*v + 32*u*u + 2624*u + 5280
for rho in [F(2), F(3, 5), F(-7, 3)]:
    t = (4 - rho)/rho; u = t*t; r = rho*rho; s = u + 15
    R = r*r*(32*u*u + 2624*u + 5280) - 1024*(3*r*s*(1+r) - 40*(1+r+r*r))
    v = R/(128*r*r)
    print(v == 2*t**3, end=' ')
    tp = 4*rho - 1
    Up = r*s - 15; Vp = (32*Up*Up + 2624*Up + 5280 - r*r*J4f(u, v))/128
    print(Up == tp*tp, Vp == 2*tp**3)
