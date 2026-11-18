# 2-adic Kummer image of E_l: y^2 = x(x-l)(x+3l), classes of (x+3l, x-l) in Q_2^*/Q_2^*2.
# Sample x = a/2^k, check 2-adic squareness of the cubic, record classes.
from fractions import Fraction as F
def v2(n):
    n=abs(n); c=0
    while n%2==0: n//=2; c+=1
    return c
def cls(q):  # q nonzero Fraction -> (v mod 2, unit mod 8)
    a,b=q.numerator,q.denominator
    v=v2(a)-v2(b); a//=2**v2(a); b//=2**v2(b)
    return (v%2, (a*b)%8)
def issq(q):
    if q==0: return True
    c=cls(q); return c==(0,1)
for l in [3,7,11,15,19,23,27,31]:
    img=set()
    for k in range(0,8):
        for a in range(-2000,2000):
            x=F(a,2**k)
            if x in (0,l,-3*l): continue
            c=x*(x-l)*(x+3*l)
            if issq(c): img.add((cls(x+3*l),cls(x-l)))
    # torsion
    img.add((cls(F(4*l)),cls(F(4*l*l))))
    img.add((cls(F(3)),cls(F(-4*l))))
    img.add((cls(F(3*l)),cls(F(-l))))
    print(l%32, len(img), sorted(img))
