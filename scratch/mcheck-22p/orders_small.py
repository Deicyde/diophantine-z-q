"""mcheck-22p step 2: orders d1, d2 of E: y^2 = x^3 - (75-53 sqrt2)^2 x at the two primes above
a split p, by direct point counting (#E = p + 1 + sum_x legendre(x^3 - delta^2 x)).
Samples (each <= 30 primes, run one after another):
  S1: the first 30 primes p > 324 with p = 1 mod 8, p = 3 mod 7 (the residues c_2, c_7 of tex L1331);
  S2: the first 30 primes p > 324 with p = 1 mod 8, p != 3 mod 7 (contrast: (7/p) may be +1);
Checks the claims of tex L1543-1582."""
from nt import is_prime as isprime, sqrt_mod, legendre as legendre_symbol
from math import gcd, isqrt

def count(p, delta):
    d2 = delta * delta % p
    s = 0
    for x in range(p):
        v = (x * x * x - d2 * x) % p
        if v:
            s += 1 if pow(v, (p - 1) // 2, p) == 1 else -1
    return p + 1 + s

def oddpart(n):
    while n % 2 == 0:
        n //= 2
    return n

def run(sample, label):
    print(f"== {label}")
    allok = True
    for p in sample:
        r = sqrt_mod(2, p)
        D1, D2 = (75 - 53 * r) % p, (75 + 53 * r) % p
        good = D1 != 0 and D2 != 0
        d1, d2 = count(p, D1), count(p, D2)
        chi7 = legendre_symbol(7, p)
        a = (p + 1 - d1) // 2 if (p + 1 - d1) % 2 == 0 else None
        isa = a is not None and isqrt(p - a * a) ** 2 == p - a * a
        g = gcd(d1, d2)
        line = (f"p={p} p%8={p%8} p%7={p%7} (7/p)={chi7} good={good} d1={d1} d2={d2} "
                f"sum==2(p+1):{d1+d2==2*(p+1)} gcd={g} p|d1d2:{(d1*d2)%p==0} a={a} a^2+b^2=p:{isa}")
        if chi7 == -1:
            pred = 4 * oddpart(gcd(abs(a), p + 1))
            line += f" pred_gcd=4*odd(gcd(a,p+1))={pred} match:{pred==g}"
            ok = good and d1 + d2 == 2 * (p + 1) and isa and pred == g and (d1 * d2) % p != 0 \
                and g % 8 == 4
            allok &= ok
        print(line)
    print(f"all checks pass for (7/p)=-1 rows: {allok}")

S1 = [p for p in range(325, 10**6) if isprime(p) and p % 8 == 1 and p % 7 == 3][:30]
S2 = [p for p in range(325, 10**6) if isprime(p) and p % 8 == 1 and p % 7 != 3][:30]
run(S1, "S1: p=1 mod 8, p=3 mod 7")
run(S2, "S2: p=1 mod 8, p!=3 mod 7")
