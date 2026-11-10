# Checks the explicit 2-adic points used for d = 5 (mod 8) and the case analysis at 2.
from fractions import Fraction as F
import random
def v2(r):
    r = F(r); n, m = r.numerator, r.denominator; k = 0
    while n % 2 == 0: n//=2; k+=1
    while m % 2 == 0: m//=2; k-=1
    return k
def cls2(r):
    r = F(r); k = v2(r); u = r / F(2)**k
    um = (u.numerator * pow(u.denominator, -1, 8)) % 8
    return (k % 2, um)   # class of r in Q2*/Q2*^2 as (v mod 2, unit mod 8)
def sq2(r): return cls2(r) == (0, 1)
def name(c):  # integer representative in {1,3,5,7,2,6,10,14}
    return c[1] * (2 if c[0] else 1)
random.seed(1)
bad = 0
for d in [5, 13, 21, 29, 37, 45, 53, 61, 69, 77, 85, 93, 101]:
    pts = [F(1,4)]
    x = F(1,4)
    pts += [-F(d*d)/x, d*(x+d)/(x-d), -d*(x-d)/(x+d)]
    got = []
    for x in pts:
        f = x*(x-d)*(x+d)
        assert sq2(f), (d, x)
        got.append((name(cls2(x)), name(cls2(x-d))))
    exp = [(1,5),(7,7),(5,10),(3,14)]
    if got != exp: bad += 1; print("mismatch", d, got)
print("explicit points: mismatches", bad)
# Case analysis: sample x in Q2 with f(x) a 2-adic square; collect classes.
allowed = {(1,1),(1,5),(7,7),(7,3),(5,10),(5,2),(3,6),(3,14)}
for d in [5, 13, 21, 29, 45, 77]:
    seen = set()
    for k in range(-6, 7):
        for u in range(1, 2**12, 2):
            x = F(u) * F(2)**k
            if x in (0, d, -d): continue
            f = x*(x-d)*(x+d)
            # f known to precision 2^(12+...) ; class decided by v and unit mod 8, fine for |k|<=6
            if sq2(f):
                seen.add((name(cls2(x)), name(cls2(x-d))))
    print(d, sorted(seen), seen == allowed)
