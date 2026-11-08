"""Fixed good slopes with no odd contact prime outside S_ht = {p <= 324}: they satisfy
GoodSlope (PatternSlopes.lean) with P = {} for every B0, since catalogue primes exceed 324.
Conditions: t not in C u {1}; |v_q(t-1)| <= 4 and |v_q(F(t)/(t-1)^8)| <= 32 for q <= 324;
every prime factor of every t - c is <= 324 or occurs to even power."""
from fractions import Fraction
from sympy import factorint, primerange

C = [0, -15, -20, -24, -30, -60]
SHT = set(primerange(2, 325))

def vq(x, q):
    n, d, e = abs(x.numerator), x.denominator, 0
    while n % q == 0: n //= q; e += 1
    while d % q == 0: d //= q; e -= 1
    return e

def free(t):
    if t in C or t == 1:
        return False
    Fq = Fraction(1)
    for c in C:
        Fq *= t - c
    Fq /= (t - 1) ** 8
    for q in SHT:
        if abs(vq(t - 1, q)) > 4 or abs(vq(Fq, q)) > 32:
            return False
    for c in C:
        x = t - c
        for n in (abs(x.numerator), x.denominator):
            for p, e in factorint(n).items():
                if p not in SHT and e % 2:
                    return False
    return True

print("t = -10 free good slope:", free(Fraction(-10)))
ints = [t for t in range(-200, 201) if free(Fraction(t))]
print(f"integers in [-200, 200] that are free good slopes: {len(ints)}; first few: {ints[:12]}")
