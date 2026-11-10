"""Densities of the condition sets, primes p <= N (description of GoodSlopePrime from lemmas.py, check E).
C   = {p = 1 (8), (p/7) = -1}
G   = C with gcd(c, p+1) = 1  (p = c^2 + e^2, c odd)        [= GoodSlopePrime for p != 7]
G*_L= G with p != -1 (mod l) for primes 5 <= l <= L, l = 1 (4)
Bad_l = {p in C : l | c, l | p+1}
"""
import math, sys
N = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10**7

def sieve(n):
    s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
    for i in range(2, int(n ** .5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return s
S = sieve(N)
primes = [i for i in range(2, N + 1) if S[i]]
small = [l for l in primes if l < 10**5]

def two_squares_odd(p):
    g = 2
    while pow(g, (p-1)//2, p) != p-1: g += 1
    i = pow(g, (p-1)//4, p)
    a, b = p, i
    while b*b > p: a, b = b, a % b
    c = b; e = math.isqrt(p - c*c)
    return (c, e) if c % 2 else (e, c)

def factor_primes(n):
    out = []
    for l in small:
        if l*l > n: break
        if n % l == 0:
            out.append(l)
            while n % l == 0: n //= l
    if n > 1: out.append(n)
    return out

piN = len(primes)
C = []; badls = {}   # p -> list of bad l
for p in primes:
    if p % 8 == 1 and pow(p % 7, 3, 7) == 6:
        C.append(p)
        c, e = two_squares_odd(p)
        g = math.gcd(c, p + 1)
        if g > 1: badls[p] = factor_primes(g)
G = [p for p in C if p not in badls]
print(f"N = {N:.1e}, pi(N) = {piN}")
print(f"|C|/pi = {len(C)/piN:.5f} (1/8 = 0.125);  |G|/pi = {len(G)/piN:.5f};  |G|/|C| = {len(G)/len(C):.5f}")
ep = 1.0
for l in small:
    if l % 4 == 1: ep *= 1 - 2/(l-1)**2
print(f"Euler product prod_(l=1(4)) (1-2/(l-1)^2) = {ep:.5f};  times 1/8 = {ep/8:.5f}")
assert all(l % 4 == 1 for ls in badls.values() for l in ls), "bad l = 3 mod 4 found"
print("every bad l is 1 mod 4: VERIFIED on this range")
for L in [5, 13, 29, 50, 100, 1000]:
    Ls = [l for l in small if 5 <= l <= L and l % 4 == 1]
    Gs = [p for p in G if all((p + 1) % l for l in Ls)]
    main = 1/8
    for l in Ls: main *= (l-2)/(l-1)
    tail = 1.0
    for l in small:
        if l > L and l % 4 == 1: tail *= 1 - 2/(l-1)**2
    print(f"L={L:5d}: |G*_L|/pi = {len(Gs)/piN:.5f};  predicted main*tail = {main*tail:.5f};  main term delta_L = {main:.5f}")
print("Bad_l counts: l, |Bad_l|, predicted 2|C|/(l-1)^2")
for l in [5, 13, 17, 29, 37, 101, 197, 401]:
    b = sum(1 for ls in badls.values() if l in ls)
    print(f"  {l:4d} {b:6d} {2*len(C)/(l-1)**2:9.1f}")
# empirical sieve constant: max over l in (L0, N^(1/4)] of |Bad_l| l^2 log N / N
L0 = 13; lmax = int(N ** 0.25)
cnt = {}
for ls in badls.values():
    for l in ls: cnt[l] = cnt.get(l, 0) + 1
ratios = [(cnt.get(l, 0) * l * l * math.log(N) / N, l) for l in small if L0 < l <= lmax and l % 4 == 1]
print(f"max_(13 < l <= N^(1/4)) |Bad_l| l^2 log N / N = {max(ratios)[0]:.3f} at l = {max(ratios)[1]}  (heuristic value 2/8 = 0.25)")
big = sum(1 for ls in badls.values() if max(ls) > lmax)
print(f"primes of C bad at some l > N^(1/4) = {lmax}: {big}  ({big/piN:.2e} of pi(N); N^(3/4)/pi = {N**0.75/piN:.2e})")
for L in [13, 50, 100]:
    t = sum(1 for ls in badls.values() if max(ls) > L)
    print(f"tail: primes of C bad at some l > {L}: {t/piN:.5f} of pi(N); sum_(l>L, l=1(4)) 2/(8(l-1)^2) = {sum(2/(8*(l-1)**2) for l in small if l > L and l % 4 == 1):.5f}")
