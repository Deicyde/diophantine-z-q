"""h29-split numeric checks: Hurwitz quaternions of odd prime norm p (as 2*alpha = (a,b,c,d),
a = b = c = d mod 2, a^2+b^2+c^2+d^2 = 4p, |coords| <= 2p, i.e. the Lean `hurwitzNorm p`) number 24(p+1);
apE p (Lean: -sum_{x<p} jacobi(x^3-x, p)) equals p + 1 - #E(F_p) for E: y^2 = x^3 - x."""
from itertools import product
from sympy import jacobi_symbol, primerange

def hurwitz_count(p):
    R = range(-2 * p, 2 * p + 1)
    c = 0
    for a, b, cc, d in product(R, repeat=4):
        if (a - b) % 2 == 0 and (a - cc) % 2 == 0 and (a - d) % 2 == 0 and a*a + b*b + cc*cc + d*d == 4 * p:
            c += 1
    return c

def apE(p):
    return -sum(jacobi_symbol((x**3 - x) % p, p) for x in range(p))

def ap_count(p):
    pts = 1 + sum(1 for x in range(p) for y in range(p) if (y*y - (x**3 - x)) % p == 0)
    return p + 1 - pts

for p in primerange(3, 14):
    print(p, hurwitz_count(p), 24 * (p + 1), apE(p), ap_count(p))

# The three-square leaf `LegendreJonesPall` on 30 squarefree inputs: n = a^2+b^2+c^2 with 4 | c when n = 1 mod 8
# (for n = 3 mod 8 every representation has a, b, c odd).
from sympy import factorint
def sqfree(n): return all(e == 1 for e in factorint(n).values())
def rep(n):
    import math
    r = int(math.isqrt(n))
    for c in range(0, r + 1):
        if n % 8 == 1 and c % 4: continue
        for b in range(0, r + 1):
            a2 = n - c*c - b*b
            if a2 < 0: break
            a = math.isqrt(a2)
            if a*a == a2: return (a, b, c)
    return None
sample = [n for n in range(1, 100000) if n % 8 in (1, 3) and sqfree(n)]
import random
random.seed(29)
pick = sorted(random.sample(sample, 30))
print([(n, rep(n)) for n in pick])
print("all represented:", all(rep(n) is not None for n in pick))
