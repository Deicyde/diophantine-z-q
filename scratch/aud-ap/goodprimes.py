#!/usr/bin/env python3
"""Independent check of the Lean predicate ZInQ.GoodSlopePrime.

(1) Literal transcription of the Lean definition (point counts over ZMod p, existential over the
    roots r of r^2 = 2) for all p < LIT, compared with the CM description of nt-22p §2.1:
    p = 1 mod 8, (7/p) = -1, and no odd l dividing gcd(a, p+1) where p = a^2 + b^2, a odd.
(2) Relative density of the CM description among primes up to DEN.
(3) Longest arithmetic progressions of good primes > 324 found up to AP (sanity: no local
    obstruction to long progressions inside the set).
"""
import math
import sys

LIT = int(sys.argv[1]) if len(sys.argv) > 1 else 6000
DEN = int(sys.argv[2]) if len(sys.argv) > 2 else 2_000_000
APB = int(sys.argv[3]) if len(sys.argv) > 3 else 200_000


def sieve(n):
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(range(i * i, n + 1, i)))
    return s


def point_count(p, a):
    """#{(x, y) in F_p^2 : y^2 = x^3 + a x} + 1, by a table of square counts."""
    sq = [0] * p
    for y in range(p):
        sq[y * y % p] += 1
    return sum(sq[(x * x * x + a * x) % p] for x in range(p)) + 1


def good_literal(p):
    """Lean: p.Prime ∧ ∃ r : ZMod p, r^2 = 2 ∧ 75-53r ≠ 0 ∧ 75+53r ≠ 0 ∧ gcd(#E_-, #E_+) = 4."""
    for r in range(p):
        if (r * r - 2) % p:
            continue
        dm, dp = (75 - 53 * r) % p, (75 + 53 * r) % p
        if dm == 0 or dp == 0:
            continue
        n1 = point_count(p, (-dm * dm) % p)
        n2 = point_count(p, (-dp * dp) % p)
        if math.gcd(n1, n2) == 4:
            return True
    return False


def two_squares(p):
    """p = a^2 + b^2 with a odd (p = 1 mod 4), by Cornacchia."""
    for c in range(2, p):
        if pow(c, (p - 1) // 2, p) == p - 1:
            break
    x = pow(c, (p - 1) // 4, p)
    a0, b0 = p, x
    lim = math.isqrt(p)
    while b0 > lim:
        a0, b0 = b0, a0 % b0
    b = b0
    a = math.isqrt(p - b * b)
    assert a * a + b * b == p
    return (a, b) if a % 2 else (b, a)


def odd_part(n):
    while n % 2 == 0:
        n //= 2
    return n


def good_cm(p):
    if p % 8 != 1 or pow(7, (p - 1) // 2, p) != p - 1:
        return False
    a, b = two_squares(p)
    return odd_part(math.gcd(a, p + 1)) == 1


def main():
    s = sieve(max(LIT, DEN, APB))
    # (1) literal vs CM, for 324 < p < LIT, and the literal set below 324
    mism, nlit, small = [], 0, []
    for p in range(2, LIT):
        if not s[p]:
            continue
        g = good_literal(p)
        if p <= 324:
            if g:
                small.append(p)
            continue
        nlit += g
        if g != good_cm(p):
            mism.append(p)
    print(f"(1) literal Lean predicate vs CM description, 324 < p < {LIT}: "
          f"{nlit} good, mismatches {mism[:10]} ({len(mism)})")
    print(f"    good primes <= 324 under the literal predicate: {small}")
    # (2) density
    npr = ngood = 0
    for p in range(325, DEN):
        if s[p]:
            npr += 1
            ngood += good_cm(p)
    print(f"(2) good / primes in (324, {DEN}): {ngood}/{npr} = {ngood / npr:.4f}")
    euler = 0.125
    for l in range(5, min(10 ** 6, len(s)), 4):
        if s[l]:
            euler *= 1 - 2 / (l - 1) ** 2
    print(f"    (1/8) prod_(l = 1 mod 4, l < min(1e6, bound)) (1 - 2/(l-1)^2) = {euler:.4f}")
    # (3) longest progression of good primes in (324, APB)
    G = [p for p in range(325, APB) if s[p] and good_cm(p)]
    Gs = set(G)
    best = (0, None, None)
    for i, x in enumerate(G):
        for y in G[i + 1:i + 400]:
            v = y - x
            k = 2
            while x + k * v in Gs:
                k += 1
            if k > best[0]:
                best = (k, x, v)
    k, x, v = best
    print(f"(3) longest progression found in (324, {APB}): length {k}, x = {x}, v = {v}, "
          f"terms {[x + j * v for j in range(k)]}")


if __name__ == "__main__":
    main()
