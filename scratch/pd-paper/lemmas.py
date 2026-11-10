"""Check the elementary character-sum lemmas behind the arithmetic description of GoodSlopePrime.
phi_p(a) = sum_x chi(x^3 + a x).  Checks, for every prime 3 <= p < PMAX:
 (A) pointCount p a (literal: #{(x,y): y^2 = x^3 + a x} + 1) = p + 1 + phi(a)   [sampled a]
 (B) phi(a k^2) = chi(k) phi(a)                                                [sampled a,k]
 (C) p = 1 mod 4  =>  phi(1) = 2 mod 4
 (D) p = 1 mod 4  =>  phi(1)^2 + phi(r)^2 = 4p for a non-square r; phi even
 (E) literal GoodSlopePrime p  <=>  [p = 1 (8), (p/7) = -1, gcd(c, p+1) = 1 where p = c^2+e^2, c odd]
     for all primes p < PMAX except p = 2, 7 handled literally.
"""
import math, random, sys
PMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 1200
random.seed(1)

def primes_upto(n):
    s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
    for i in range(2, int(n ** .5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(n + 1) if s[i]]

def literal_pointcount(p, a, sq):
    # sq[c] = #{y in Z/p : y^2 = c}; literal count of affine solutions + 1
    return sum(sq[(x*x*x + a*x) % p] for x in range(p)) + 1

def literal_good(p):
    sq = [0]*p
    for y in range(p): sq[y*y % p] += 1
    for r in range(p):
        if (r*r - 2) % p: continue
        d1, d2 = (75 - 53*r) % p, (75 + 53*r) % p
        if d1 == 0 or d2 == 0: continue
        n1 = literal_pointcount(p, (-d1*d1) % p, sq); n2 = literal_pointcount(p, (-d2*d2) % p, sq)
        if math.gcd(n1, n2) == 4: return True
    return False

def two_squares_odd(p):
    # p = c^2 + e^2 with c odd (p = 1 mod 4)
    for g in range(2, p):
        if pow(g, (p-1)//2, p) == p-1: break
    i = pow(g, (p-1)//4, p)
    a, b = p, i
    while b*b > p: a, b = b, a % b
    c, e = b, int(math.isqrt(p - b*b))
    assert c*c + e*e == p
    return (c, e) if c % 2 else (e, c)

def description(p):
    if p % 8 != 1 or pow(p % 7, 3, 7) != 6: return False   # (p/7) = -1  <=> (p mod 7)^3 = -1
    c, e = two_squares_odd(p)
    return math.gcd(c, p + 1) == 1

bad = {k: 0 for k in 'ABCDE'}; nA = nB = nC = nD = nE = 0
for p in primes_upto(PMAX):
    if p == 2: continue
    chi = [0] + [1 if pow(x, (p-1)//2, p) == 1 else -1 for x in range(1, p)]
    phi = lambda a: sum(chi[(x*x*x + a*x) % p] for x in range(p))
    sq = [0]*p
    for y in range(p): sq[y*y % p] += 1
    for _ in range(3):
        a = random.randrange(p); nA += 1
        if literal_pointcount(p, a, sq) != p + 1 + phi(a): bad['A'] += 1
        k = random.randrange(1, p); nB += 1
        if phi(a*k*k % p) != chi[k]*phi(a): bad['B'] += 1
    if p % 4 == 1:
        r = next(x for x in range(2, p) if chi[x] == -1)
        f1, fr = phi(1), phi(r); nC += 1; nD += 1
        if f1 % 4 != 2: bad['C'] += 1
        if f1*f1 + fr*fr != 4*p or f1 % 2 or fr % 2: bad['D'] += 1
    if p < PMAX:
        nE += 1
        lg = literal_good(p); de = description(p) if p not in (2, 7) else False
        if lg != de: bad['E'] += 1; print('mismatch E', p, lg, de)
print('tests: A', nA, 'B', nB, 'C', nC, 'D', nD, 'E', nE)
print('failures:', bad)
