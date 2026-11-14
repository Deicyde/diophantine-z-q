# Multiplication table of the generators x4, x6, x4^{-1}, x6^{-1} on the representatives 1, x4, x6, x4 x6
# of N_B(O)^+ / Q^x O^1, B = (2,-3): g * rep_i = r * rep_k * u with r in Q_{>0}, u in O, nrd u = 1.
from fractions import Fraction as F
import math
A, Bc = 2, -3
def mul(x, y):
    a1,b1,c1,d1 = x; a2,b2,c2,d2 = y
    return (a1*a2 + A*b1*b2 + Bc*c1*c2 - A*Bc*d1*d2,
            a1*b2 + b1*a2 - Bc*(c1*d2 - d1*c2),
            a1*c2 + c1*a2 + A*(b1*d2 - d1*b2),
            a1*d2 + d1*a2 + b1*c2 - c1*b2)
def nrd(x): a,b,c,d = x; return a*a - 2*b*b + 3*c*c - 6*d*d
def conj(x): a,b,c,d = x; return (a,-b,-c,-d)
def sc(q,x): return tuple(q*t for t in x)
def inv(x): return sc(F(1)/nrd(x), conj(x))
def coords(x):
    a,b,c,d = x; return (a - c, b - d, 2*c, 2*d)
def inO(x): return all(F(t).denominator == 1 for t in coords(x))
one = (F(1),F(0),F(0),F(0))
x4 = (F(1),F(1),F(1),F(0)); x6 = (F(-3,2),F(0),F(1,2),F(0))
reps = [one, x4, x6, mul(x4,x6)]
gens = {'x4':x4, 'x6':x6, 'x4i':inv(x4), 'x6i':inv(x6)}
def sqfree_class(q):
    q = F(q); n, d = q.numerator*q.denominator, 1
    cls = 1
    for p in (2,3):
        e = 0
        while n % p == 0: n//=p; e+=1
        if e % 2: cls *= p
    return cls
cls_of = {1:0, 2:1, 3:2, 6:3}
print("inv x4 =", inv(x4), " inv x6 =", inv(x6))
for gname, g in gens.items():
    for i, r_i in enumerate(reps):
        y = mul(g, r_i); n = nrd(y)
        k = cls_of[sqfree_class(n)]
        r2 = n / nrd(reps[k]); r = F(math.isqrt(r2.numerator), math.isqrt(r2.denominator))
        assert r*r == r2
        u = sc(1/r, mul(inv(reps[k]), y))
        assert mul(sc(r, reps[k]), u) == y and nrd(u) == 1
        print(gname, i, "-> k =", k, " r =", r, " u =", u, " inO:", inO(u), " coords", coords(u))
