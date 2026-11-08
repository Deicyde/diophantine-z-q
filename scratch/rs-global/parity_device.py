"""The parity device behind the pole predicate (manuscript Lemma 5.1, line 988).

For f_n(x, e) = x * prod_{i=1..n} (x - a_i e) with fixed unit coefficients a_i, odd p, v_p(e) even
and v_p(x) odd, the claim is: v_p(f_n) is odd for every such (x, e) iff n is even.
n = 2 is the manuscript's curve x(x - e)(x + 3e); n = 1 is a conic.
Also checks the asymmetry of H = A(A - B^2) used in Lemma 5.1.
"""
import random
from fractions import Fraction

def vp(q, p):
    q = Fraction(q)
    if q == 0:
        return 10**9
    a, b, v = q.numerator, q.denominator, 0
    while a % p == 0:
        a //= p; v += 1
    while b % p == 0:
        b //= p; v -= 1
    return v

random.seed(1)
p = 11
coeffs = {1: [1], 2: [1, -3], 3: [1, -3, 2], 4: [1, -3, 2, 5]}
for n, a in coeffs.items():
    fails = 0
    trials = 0
    for _ in range(3000):
        ex = random.choice([-7, -5, -3, -1, 1, 3, 5, 7])
        ee = random.choice([-8, -6, -4, -2, 0, 2, 4, 6, 8])
        unit = lambda: Fraction(random.choice([1, 2, 3, 4, 5, 6, 7, 8, 9, 10]) + p * random.randint(0, 50),
                                random.choice([1, 2, 3, 4, 5, 6, 7, 8, 9, 10]))
        x = unit() * Fraction(p) ** ex
        e = unit() * Fraction(p) ** ee
        f = x
        for ai in a:
            f *= (x - ai * e)
        trials += 1
        if f != 0 and vp(f, p) % 2 == 0:
            fails += 1
    print("n = %d: even valuation of f in %d of %d trials (v(e) even, v(x) odd)" % (n, fails, trials))

# asymmetry: v(B) = k odd; m a p-unit; A = mB, H = A(A - B^2)
for k in [-5, -3, -1, 1, 3, 5]:
    B = Fraction(3, 7) * Fraction(p) ** k
    A = 2 * B
    H = A * (A - B * B)
    print("v(B) = %2d: v(A) = %2d, v(H) = %2d, parities of v(A), v(H): %d %d" %
          (k, vp(A, p), vp(H, p), vp(A, p) % 2, vp(H, p) % 2))
