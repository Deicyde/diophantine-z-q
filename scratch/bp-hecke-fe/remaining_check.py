# Numerical check of the two remaining hypotheses of literature_hecke_fe_of_heckeEuler_gaussSplit.
# heckeCoeff d n = 1/4 sum_{a^2+b^2=n} jacobi(n,d) unitOf(a,b) (a+bi)
# GaussSplit 1: for primes p = 1 mod 4: p - #{(x,y) in F_p^2 : y^2 = x^3 - x} = heckeCoeff 1 p
# HeckeEuler d: heckeCoeff d n = prod_{p^k || n} [T^k] 1/(1 - heckeCoeff(d,p) T + p T^2)  (1 if p | 2d)
import cypari2
pari = cypari2.Pari()
def unit(a, b):
    t = (a % 4, b % 4)
    if t in [(1,0),(3,2)]: return 1
    if t in [(3,0),(1,2)]: return -1
    if t in [(0,3),(2,1)]: return 1j
    if t in [(0,1),(2,3)]: return -1j
    return 0
def hecke(d, n):
    s = 0; r = int(n**0.5) + 1
    for a in range(-r, r+1):
        for b in range(-r, r+1):
            if a*a + b*b == n:
                s += int(pari.kronecker(n, d)) * unit(a, b) * complex(a, b)
    return s / 4
bad = 0; cnt = 0
for p in range(5, 300):
    if not pari.isprime(p) or p % 4 != 1: continue
    N = sum(1 for x in range(p) for y in range(p) if (y*y - (x**3 - x)) % p == 0)
    cnt += 1
    if abs((p - N) - hecke(1, p)) > 1e-9: bad += 1
print("GaussSplit 1: primes p = 1 mod 4, p < 300: %d checked, %d failures" % (cnt, bad))
def euler_coeff(ap, p, k, bad_prime):
    if bad_prime: return 1 if k == 0 else 0
    c = [1, ap]
    for j in range(2, k+1): c.append(ap*c[-1] - p*c[-2])
    return c[k]
for d in [5, 13, 21, 29]:
    bad = 0
    for n in range(1, 301):
        f = pari.factor(n); prod = 1
        for i in range(len(f[0])):
            p, k = int(f[0][i]), int(f[1][i])
            prod *= euler_coeff(hecke(d, p), p, k, (2*d) % p == 0)
        if abs(prod - hecke(d, n)) > 1e-6: bad += 1
    print("HeckeEuler d=%d, n <= 300: %d failures" % (d, bad))
