"""Small number-theory helpers (no external dependencies beyond numpy)."""
import numpy as np
from math import gcd, isqrt

def primes_upto(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, isqrt(n) + 1):
        if s[i]:
            s[i*i::i] = False
    return np.nonzero(s)[0]

def sieve(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, isqrt(n) + 1):
        if s[i]:
            s[i*i::i] = False
    return s

_MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)

def is_prime(n):
    """Deterministic Miller-Rabin for n < 3.3e24."""
    if n < 2:
        return False
    for p in _MR_BASES:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2; s += 1
    for a in _MR_BASES:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True

def legendre(a, p):
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1

def sqrt_mod(a, p):
    """Tonelli-Shanks; p odd prime, a a QR."""
    a %= p
    if a == 0:
        return 0
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2; s += 1
    z = 2
    while legendre(z, p) != -1:
        z += 1
    m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1:
            t2 = t2 * t2 % p; i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c, t, r = i, b * b % p, t * b * b % p, r * b % p
    return r

def two_squares(p):
    """p = 1 mod 4 prime: return (a, b) with a^2 + b^2 = p, a odd, b even, a, b > 0."""
    x = sqrt_mod(p - 1, p)
    r0, r1 = p, x
    lim = isqrt(p)
    while r1 > lim:
        r0, r1 = r1, r0 % r1
    a = r1
    b = isqrt(p - a * a)
    assert a * a + b * b == p
    if a % 2 == 0:
        a, b = b, a
    return a, b

def odd_part(n):
    n = abs(n)
    while n % 2 == 0:
        n //= 2
    return n

def good_cm(p):
    """Predicted goodness from the CM description: p = 1 mod 8, (p/7) = -1,
    and gcd(a, p+1) has no odd prime factor, where p = a^2 + b^2 with a odd."""
    if p % 8 != 1 or legendre(p, 7) != -1:
        return False
    a, b = two_squares(p)
    return odd_part(gcd(a, p + 1)) == 1
