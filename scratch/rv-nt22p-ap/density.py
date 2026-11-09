# Independent check of section 2.1-2.2 of nt-22p: the CM description of GoodSlopePrime and the density.
import sys, math
import cypari2
pari = cypari2.Pari()
pari.allocatemem(2*10**9)

def brute_count(p, a):
    # number of (x,y) in F_p^2 with y^2 = x^3 + a x, plus 1  (pointCount of PrimePattern.lean)
    sq = [0]*p
    for y in range(p): sq[y*y % p] += 1
    return 1 + sum(sq[(x*x*x + a*x) % p] for x in range(p))

def roots2(p, fast):
    if not fast: return [r for r in range(p) if (r*r - 2) % p == 0]
    if pari.kronecker(2, p) != 1: return []
    r = int(pari.lift(pari.sqrt(pari.Mod(2, p)))); return [r, p - r]

def good_literal(p, counter, fast=False):
    # GoodSlopePrime p: exists r, r^2=2, 75-53r != 0, 75+53r != 0, gcd(N(-(75-53r)^2), N(-(75+53r)^2)) = 4
    for r in roots2(p, fast):
        d1, d2 = (75 - 53*r) % p, (75 + 53*r) % p
        if d1 == 0 or d2 == 0: continue
        n1 = counter(p, (-d1*d1) % p); n2 = counter(p, (-d2*d2) % p)
        if math.gcd(n1, n2) == 4: return True
    return False

def pari_count(p, a):
    return int(pari.ellcard(pari.ellinit([0, 0, 0, a, 0], p)))

def good_cm(p):
    if p % 8 != 1: return False
    if pow(7, (p-1)//2, p) == 1: return False
    s = pari.qfbsolve(pari.Qfb(1, 0, 1), p)
    a, b = int(s[0]), int(s[1])
    if a % 2 == 0: a, b = b, a
    g = math.gcd(a, p + 1)
    while g % 2 == 0: g //= 2
    return g == 1

mode = sys.argv[1]
if mode == 'brute':   # literal definition with brute-force point counts vs CM description
    N = int(sys.argv[2]); mism = 0; ng = 0
    for p in pari.primes([1, N]):
        p = int(p)
        if p < 3: continue
        L = good_literal(p, brute_count)
        if p > 324 and L != good_cm(p): mism += 1; print('mismatch', p, L)
        ng += L
    print('brute up to', N, 'good:', ng, 'mismatches (p>324):', mism)
elif mode == 'pari':
    N = int(sys.argv[2]); mism = 0; ng = 0; small = []
    for p in pari.primes([1, N]):
        p = int(p)
        if p < 3: continue
        L = good_literal(p, pari_count, True)
        if p <= 324 and L: small.append(p)
        if p > 324 and L != good_cm(p): mism += 1; print('mismatch', p, L)
        ng += L
    print('pari up to', N, 'good:', ng, 'mismatches (p>324):', mism, 'good p<=324:', small)
elif mode == 'density':
    N = int(sys.argv[2]); tot = cls = g = 0
    for p in pari.primes([1, N]):
        p = int(p)
        if p < 11: continue
        tot += 1
        if p % 8 == 1 and pow(7, (p-1)//2, p) != 1:
            cls += 1; g += good_cm(p)
    print('N', N, 'primes', tot, 'class share', cls/tot, 'good share', g/tot, 'good/class', g/cls)
    E = 1.0
    for l in pari.primes([1, 10**7]):
        l = int(l)
        if l % 4 == 1: E *= 1 - 2/(l-1)**2
    print('Euler product up to 1e7 (tail < 2/(4*1e7)):', E, ' times 1/8:', E/8)
