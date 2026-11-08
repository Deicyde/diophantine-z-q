"""Independent check of the configurations found by psearch, against the scaled analogue
of GoodSlope (PatternSlopes.lean) with the old primes S = {2, 3, 5, 7}, B_q = 4:
  t not in C u {1}; |v_q(t - 1)| <= 4 and |v_q(F(t)/(t-1)^8)| <= 32 for q in S;
  every odd contact prime p outside S has contact valuation 1 and is good;
  at most six odd contact primes.
Goodness uses the CM criterion checked against point counts in good_primes.py.
"""
import sys, re
from fractions import Fraction
from sympy import factorint
from ntlib import good_cm

S = [2, 3, 5, 7]
C = [0, -15, -20, -24, -30, -60]

def vq(x, q):
    x = Fraction(x)
    if x == 0:
        raise ValueError
    n, d, e = abs(x.numerator), x.denominator, 0
    while n % q == 0: n //= q; e += 1
    while d % q == 0: d //= q; e -= 1
    return e

def good_slope(t):
    assert t not in C and t != 1
    Fq = Fraction(1)
    for c in C:
        Fq *= (t - c)
    Fq /= (t - 1) ** 8
    for q in S:
        assert abs(vq(t - 1, q)) <= 4 and abs(vq(Fq, q)) <= 32, ("old", t, q)
    odd = set()
    for c in C:
        x = t - c
        for p, e in factorint(abs(x.numerator)).items():
            if p in S or e % 2 == 0:
                continue
            assert e == 1 and good_cm(p), ("contact", t, c, p, e)
            odd.add(p)
    assert len(odd) <= 6
    return len(odd)

def main(path):
    n = 0
    for line in open(path):
        m = re.match(r"sum A=(-?\d+) u1=(\d+) u2=(\d+) v=(\d+)", line)
        if m:
            A, u1, u2, v = map(int, m.groups())
            ts = [Fraction(u1, v), Fraction(u2, v), Fraction(A * v - u1 - u2, v)]
        m2 = re.match(r"diff A=(-?\d+) u=(\d+) v=(\d+)", line)
        if m2:
            A, u, v = map(int, m2.groups())
            ts = [Fraction(u, v), Fraction(u, v) - A]
        m3 = re.match(r"two A=(-?\d+) u=(\d+) v=(\d+)", line)
        if m3:
            A, u, v = map(int, m3.groups())
            ts = [Fraction(u, v), A + 10 - Fraction(u, v), Fraction(-10)]
            m = m3
        if not (m or m2):
            continue
        assert (sum(ts) if m else ts[0] - ts[1]) == A
        counts = [good_slope(t) for t in ts]
        n += 1
        print(f"A={A}: slopes good, odd contact primes per slope {counts}")
    print(f"{n} configurations verified")

if __name__ == "__main__":
    main(sys.argv[1])
