# Check V16 8931-8936: for E_l: y^2=x(x-l)(x+3l), l = 11 mod 12 squarefree,
# every Q_2-point with x not in {0,l,-3l} has v2(x+3l), v2(x-l) both even.
# Sample: x = a/2^k for odd a in a box, k in [-6,6]; test 2-adic squareness of the cubic.
# Also record j-invariant and non-CM check.
import cypari2, itertools
pari = cypari2.Pari()
from fractions import Fraction
def v2(q):
    q = Fraction(q); n, d = q.numerator, q.denominator; v = 0
    while n % 2 == 0: n//=2; v+=1
    while d % 2 == 0: d//=2; v-=1
    return v
def is_sq_Q2(q):
    q = Fraction(q)
    if q == 0: return True
    v = v2(q)
    if v % 2: return False
    u = q / Fraction(2)**v
    return (u.numerator * u.denominator) % 8 == 1
ls = [l for l in range(11, 2000, 12) if pari.issquarefree(l)][:30]
bad = 0; npts = 0
for l in ls:
    E = pari.ellinit([0, 2*l, 0, -3*l*l, 0])
    assert str(E[12]) == '35152/9', E[12]
    for k in range(-6, 7):
        for a in range(-255, 256, 2):
            x = Fraction(a, 1) * Fraction(2)**k
            if x in (0, l, -3*l): continue
            c = x*(x-l)*(x+3*l)
            if is_sq_Q2(c):
                npts += 1
                if v2(x+3*l) % 2 or v2(x-l) % 2: bad += 1
print("l sample", ls)
print("2-adic points tested", npts, "violations", bad)
