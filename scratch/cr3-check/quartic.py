"""Third pass of step 4: a direct search for points with x in a Q*^2. Writing x = a u^2/t^2 with
e = d/a, y^2 = x^3 - d^2 x becomes w^2 = a (u^4 - e^2 t^4) (w = y t^3 / (a u)... up to squares), so every
point of C_d with x/a a nonzero square comes from a rational point of this quartic, and conversely
x = a u^2 / t^2. PARI hyperellratpoints with bound H, then exact recheck.
Usage: python quartic.py d a H -> appends to quartic_found.txt"""
import sys
from fractions import Fraction as Fr
from math import isqrt
import cypari2
pari = cypari2.Pari(); pari.allocatemem(2 * 10**9)
d, a, H = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
e = d // a
assert e * a == d
pts = pari('hyperellratpoints((%d)*x^4 + (%d), %d)' % (a, -a * e * e, H))
found = None
for P in pts:
    s = Fr(int(pari.numerator(P[0])), int(pari.denominator(P[0])))
    if s == 0:
        continue
    x = a * s * s
    f = x ** 3 - d * d * x
    if f >= 0 and isqrt(f.numerator) ** 2 == f.numerator and isqrt(f.denominator) ** 2 == f.denominator:
        y = Fr(isqrt(f.numerator), isqrt(f.denominator))
        r = x / a
        assert x != 0 and y * y == x ** 3 - d * d * x and isqrt(r.numerator) ** 2 == r.numerator and isqrt(r.denominator) ** 2 == r.denominator
        found = (x, y)
        break
msg = '%d %d H=%d %s' % (d, a, H, ('FOUND x = %s (%d digits in num+den)' % (found[0] if len(str(found[0])) < 80 else '...', len(str(found[0].numerator)) + len(str(found[0].denominator)))) if found else 'NOT FOUND')
print(msg, flush=True)
open('quartic_found.txt', 'a').write(msg + ('  x=%s y=%s' % found if found else '') + '\n')
