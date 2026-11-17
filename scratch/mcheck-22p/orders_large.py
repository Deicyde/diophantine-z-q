"""mcheck-22p step 2, large primes. Primes p meeting ALL residue prescriptions of tex L1330-1333
(p = 1 mod 8, p = 3 mod 7, p = 1 mod q for odd q <= 324, q != 7), so p+1 has no odd prime factor
<= 324 other than possibly ... (p+1 = 4 mod 7, = 2 mod q): every odd l | gcd(d1,d2) is > 324.
Orders: p = a^2 + b^2 (Cornacchia); #E_delta is one of p+1 +- 2a, p+1 +- 2b; the right one is
identified by testing [N]P = O on 4 random points (independent of the CM theory; we also report
whether exactly one candidate survives).
Part A: 30 random pattern primes (seeded). Part B: 3 pattern primes built so that l = 337 divides
the trace half and p+1 (so gcd(d1,d2) = 4*337): the congruence conditions alone do NOT give
gcd = 4; the sieve step of tex L1600-1643 is needed for l > L."""
import random
from math import gcd, isqrt
from nt import is_prime, sqrt_mod, legendre, primes_upto

random.seed(22)
PR = primes_upto(324)

def cornacchia(p):
    r = sqrt_mod(p - 1, p)  # sqrt(-1)
    a, b = p, r
    lim = isqrt(p)
    while b > lim:
        a, b = b, a % b
    c = isqrt(p - b * b)
    assert b * b + c * c == p
    return b, c

def ec_mul(n, P, A, p):
    # y^2 = x^3 + A x, affine, None = O
    def add(P, Q):
        if P is None: return Q
        if Q is None: return P
        x1, y1 = P; x2, y2 = Q
        if x1 == x2:
            if (y1 + y2) % p == 0: return None
            lam = (3 * x1 * x1 + A) * pow(2 * y1, -1, p) % p
        else:
            lam = (y2 - y1) * pow(x2 - x1, -1, p) % p
        x3 = (lam * lam - x1 - x2) % p
        return (x3, (lam * (x1 - x3) - y1) % p)
    R = None
    if n < 0:
        n = -n; P = (P[0], -P[1] % p)
    while n:
        if n & 1: R = add(R, P)
        P = add(P, P); n >>= 1
    return R

def rand_point(A, p):
    while True:
        x = random.randrange(p)
        f = (x ** 3 + A * x) % p
        if f and legendre(f, p) == 1:
            return (x, sqrt_mod(f, p))

def order(p, delta, a, b):
    A = (-delta * delta) % p
    cands = sorted({p + 1 - 2 * a, p + 1 + 2 * a, p + 1 - 2 * b, p + 1 + 2 * b})
    pts = [rand_point(A, p) for _ in range(4)]
    ok = [N for N in cands if all(ec_mul(N, P, A, p) is None for P in pts)]
    return ok

def oddpart(n):
    while n % 2 == 0: n //= 2
    return n

def check(p, tag):
    r = sqrt_mod(2, p)
    D1, D2 = (75 - 53 * r) % p, (75 + 53 * r) % p
    a, b = cornacchia(p)
    o1, o2 = order(p, D1, a, b), order(p, D2, a, b)
    uniq = len(o1) == 1 and len(o2) == 1
    d1, d2 = o1[0], o2[0]
    g = gcd(d1, d2)
    ah = (p + 1 - d1) // 2
    pred = 4 * oddpart(gcd(abs(ah), p + 1))
    res = dict(bits=p.bit_length(), good=bool(D1 and D2), unique=uniq, sum_ok=(d1 + d2 == 2 * (p + 1)),
               gcd=g, gcd_eq_pred=(g == pred), two_part_4=(g % 8 == 4), p_ndiv=((d1 * d2) % p != 0),
               hasse=(abs(p + 1 - d1) ** 2 <= 4 * p))
    print(tag, f"p mod 10^12 = {p % 10**12}", res)
    return res

def crt(rs, ms):
    x, M = 0, 1
    for r, m in zip(rs, ms):
        t = ((r - x) * pow(M, -1, m)) % m
        x += M * t; M *= m
    return x % M, M

# residues of tex L1330-1333
rs, ms = [1], [8]
for q in PR:
    if q == 2: continue
    rs.append(3 if q == 7 else 1); ms.append(q)
r0, M = crt(rs, ms)
print("modulus M = 8*prod odd q<=324 has", M.bit_length(), "bits")

print("== Part A: 30 random pattern primes")
allA = True; n = 0
while n < 30:
    p = r0 + M * random.randrange(1, 10**6)
    if not is_prime(p): continue
    assert all(p % q == rr % q for rr, q in zip(rs, ms))
    res = check(p, f"A{n}")
    allA &= res['good'] and res['unique'] and res['sum_ok'] and res['gcd_eq_pred'] and res['two_part_4'] and res['p_ndiv'] and res['hasse']
    n += 1
print("Part A: all structural checks pass:", allA)

print("== Part B: pattern primes with l = 337 | gcd(trace/2, p+1)")
l = 337
# a odd, l | a; b = 0 mod 4; for each odd q<=324 pick (a mod q, b mod q) with a^2+b^2 = c_q
ars, brs, mm = [1], [0], [4]  # a = 1 mod 4 (odd), b = 0 mod 4  -> p = 1 mod 8
for q in PR:
    if q == 2: continue
    c = 3 if q == 7 else 1
    found = None
    for x in range(q):
        y2 = (c - x * x) % q
        if y2 == 0 or legendre(y2, q) == 1:
            if x % q != 0 or True:
                found = (x, sqrt_mod(y2, q) if y2 else 0); break
    ars.append(found[0]); brs.append(found[1]); mm.append(q)
i = sqrt_mod(l - 1, l)
ars.append(0); brs.append(i); mm.append(l)
a0, MM = crt(ars, mm); b0, _ = crt(brs, mm)
n = 0
while n < 3:
    a = a0 + MM * random.randrange(1, 10**4); b = b0 + MM * random.randrange(1, 10**4)
    p = a * a + b * b
    if not is_prime(p): continue
    assert all(p % q == rr % q for rr, q in zip(rs, ms)) and (p + 1) % l == 0
    check(p, f"B{n}")
    n += 1
