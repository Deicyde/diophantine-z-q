"""Density of good slope primes.
Checks (i) GoodSlopePrime via point counts (PARI ellap) against the CM description
  p = 1 mod 8, (7/p) = -1, and no odd l with l | a, l | p+1  (p = a^2+b^2, a odd);
(ii) the share of good primes in the class against prod_{l = 1 mod 4} (1 - 2/(l-1)^2)."""
import cypari2, math
pari = cypari2.Pari()
pari.allocatemem(2*10**9)
N = 3*10**6
def good_pc(p):
    # GoodSlopePrime from point counts: split in Q(sqrt2), good reduction, gcd(d1,d2)=4
    if p == 2 or pari.kronecker(2, p) != 1: return False
    r = int(pari.lift(pari.sqrt(pari.Mod(2, p))))
    ds = []
    for sgn in (1, -1):
        dd = (75 - sgn*53*r) % p
        if dd == 0: return False
        E = pari.ellinit([0, 0, 0, (-dd*dd) % p, 0], p)
        ds.append(p + 1 - int(pari.ellap(E)))
    return math.gcd(ds[0], ds[1]) == 4
def good_cm(p):
    if p % 8 != 1 or pari.kronecker(7, p) != -1: return False
    a, b = [int(x) for x in pari.qfbsolve(pari.Qfb(1, 0, 1), p)]
    if a % 2 == 0: a, b = b, a
    g = math.gcd(a, p + 1)
    while g % 2 == 0: g //= 2
    return g == 1
primes = [int(x) for x in pari.primes([11, N])]
mism = 0; cls = 0; good = 0
for i, p in enumerate(primes):
    gc = good_cm(p)
    if p < 200000:
        if gc != good_pc(p): mism += 1
    if p % 8 == 1 and pari.kronecker(7, p) == -1: cls += 1
    good += gc
print(f"primes 11..{N}: {len(primes)}; point-count vs CM mismatches below 2e5: {mism}")
print(f"class p=1(8),(7/p)=-1: {cls} ({cls/len(primes):.4f} of primes; 1/8 = 0.125)")
print(f"good: {good} ({good/len(primes):.4f} of primes; {good/cls:.4f} of class)")
prod = 1.0
for l in pari.primes([3, 10**6]):
    l = int(l)
    if l % 4 == 1: prod *= 1 - 2/(l-1)**2
print(f"Euler product prod_(l=1 mod 4) (1-2/(l-1)^2) = {prod:.4f}; times 1/8 = {prod/8:.4f}")
