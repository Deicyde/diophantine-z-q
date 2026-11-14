# Structure constants of O = Z<1, i, (1+j)/2, (i+ij)/2> in B = (2,-3): coords of e_p * e_q (for inO_mul).
from fractions import Fraction as F
A, Bc = 2, -3
def mul(x, y):
    a1,b1,c1,d1 = x; a2,b2,c2,d2 = y
    return (a1*a2 + A*b1*b2 + Bc*c1*c2 - A*Bc*d1*d2, a1*b2 + b1*a2 - Bc*(c1*d2 - d1*c2),
            a1*c2 + c1*a2 + A*(b1*d2 - d1*b2), a1*d2 + d1*a2 + b1*c2 - c1*b2)
def coords(x): a,b,c,d = x; return (a - c, b - d, 2*c, 2*d)
h = F(1,2)
E = [(1,0,0,0),(0,1,0,0),(h,0,h,0),(0,h,0,h)]
names_a = ["a0","a1","a2","a3"]; names_b = ["b0","b1","b2","b3"]
out = []
for k in range(4):
    terms = []
    for p in range(4):
        for q in range(4):
            c = coords(mul(E[p],E[q]))[k]
            assert F(c).denominator == 1
            c = int(c)
            if c: terms.append(f"({c}) * {names_a[p]} * {names_b[q]}")
    out.append(" + ".join(terms) if terms else "0")
for o in out: print(o)
