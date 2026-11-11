"""E2: column property on a rational toy of the test-site pole input.
B(q) = R/Θ², R = R0 a², a = 1 - R0 q², W = Π_j (1 + R C_j²), Θ = 2/W (trace over Q of W^{-1} for rational tests).
Claim: if (R0, C) is bad at p for one p-integral q (v_p(B) < 0 odd), then it is bad for EVERY q ∈ Q.
Samples: 30 random bad data at random primes p > 324, 200 random q each (incl. q with p-power denominators)."""
import random
from fractions import Fraction as Fr
from sympy import prime
random.seed(1)
def v(p, x):
    n, d = x.numerator, x.denominator; k = 0
    if n == 0: return 10**9
    while n % p == 0: n //= p; k += 1
    while d % p == 0: d //= p; k -= 1
    return k
def B_of(R0, C, q):
    a = 1 - R0 * q * q; R = R0 * a * a
    W = Fr(1)
    for c in C: W *= 1 + R * c * c
    return R * W * W / 4
fails = 0; checked = 0
for s in range(30):
    p = prime(random.randint(70, 400))         # p in (349, ~2741)
    u = random.choice([x for x in range(1, 50) if x % p])
    R0 = Fr(p * u, random.choice([1, 9, 25]))  # v_p(R0) = 1
    C = [Fr(random.randint(1, 40), p)] + [Fr(random.randint(-30, 30), random.randint(1, 9)) for _ in range(5)]
    assert v(p, B_of(R0, C, Fr(0))) < 0 and v(p, B_of(R0, C, Fr(0))) % 2 == 1   # bad at q = 0
    for t in range(200):
        e = random.randint(0, 3)
        q = Fr(random.randint(-10**4, 10**4), random.randint(1, 50) * p**e)
        b = B_of(R0, C, q); checked += 1
        if b == 0: continue
        if not (v(p, b) < 0 and v(p, b) % 2 == 1): fails += 1
print("bad data samples: 30; (data, q) pairs checked:", checked, "; pairs NOT bad:", fails)
