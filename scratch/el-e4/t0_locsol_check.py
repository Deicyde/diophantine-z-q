# Check locsol against (a) el-cert's local obstruction lemma, (b) curves with a known rational point.
import random; from fractions import Fraction as Fr
from locsol import locsol, quartic
import cypari2; pari = cypari2.Pari()
random.seed(11); agree = tot = 0
ps = [11, 13, 17, 19, 23, 29, 31, 37, 41, 43]
while tot < 30:
    p = random.choice(ps); m = random.choice([1,-1,2,-2,3,-3,5,-5,6,-6,7,-7])
    if m % p == 0: continue
    R0 = random.randint(2, 500)
    if R0 % p == 0 or pari.kronecker(R0, p) != -1: continue
    Th = Fr(p ** random.choice([1, 2]) * random.randint(1, 50), random.randint(1, 30))
    if Th.numerator % p ** 3 == 0 and False: pass
    pred = pari.kronecker(-m, p) == -1
    got = locsol(quartic(m, Th, R0), p)
    tot += 1; agree += (got == pred)
print("lemma cases agree:", agree, "/", tot)
# (b) curves through q=0: m(m Th^2 - R0) square -> must be soluble at every p
ok = cnt = 0
for Th in range(1, 200):
    for m in (1, 2, 3, 5, 6, 7, -1, -2):
        R0 = 7 * 11
        v = m * (m * Th * Th - R0)
        if v > 0 and pari.issquare(v):
            cnt += 1
            ok += all(locsol(quartic(m, Th, R0), p) is True for p in (2, 3, 5, 7, 11, 13))
print("curves with q=0 point, soluble at 2..13:", ok, "/", cnt)
