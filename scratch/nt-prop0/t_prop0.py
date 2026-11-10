# End-to-end check of Proposition 0 in the x-form: (a, b) squarefree in the box <-1,2,p|d> is
# locally soluble (x/a, (x-d)/b, (x+d)/(ab) squares, or a, b squares) at infinity, 2 and p | d,
# computed from sampled points, iff the bits solve the system Sigma(C_d) (E1, E2, R, D for c = 5).
from fractions import Fraction as F
from itertools import product
import random
from t_fp_surj import chi
def vp(r, p):
    r = F(r); n, m, k = r.numerator, r.denominator, 0
    while n % p == 0: n //= p; k += 1
    while m % p == 0: m //= p; k -= 1
    return k
def cls(r, p):
    k = vp(r, p); u = F(r) / F(p)**k
    if p == 2: return (k % 2, (u.numerator * pow(u.denominator, -1, 8)) % 8)
    return (k % 2, chi(u.numerator * u.denominator, p))
def image(d, p):
    one = cls(1, p)
    img = {(one, one), (cls(-1,p), cls(-d,p)), (cls(d,p), cls(2,p)), (cls(-d,p), cls(-2*d,p))}
    N = 12 if p == 2 else 3
    for k in range(-4, 5):
        for u in range(1, p**N):
            if u % p == 0: continue
            x = F(u) * F(p)**k
            if x in (0, d, -d): continue
            if cls(x*(x-d)*(x+d), p) == one: img.add((cls(x,p), cls(x-d,p)))
    return img
def system(d, S, a0, a1, b0, b1, u, v):
    lam = {p: (1 if p % 4 == 3 else 0) for p in S}
    mu = {p: (1 if p % 8 in (3, 5) else 0) for p in S}
    bit = lambda y, x: 0 if chi(y, x) == 1 else 1   # [y/x]
    for x in S:
        K = lambda w: sum(bit(y, x) * (w[y] + w[x]) for y in S if y != x)
        if (K(u) + lam[x]*v[x] - a0*lam[x] - a1*mu[x]) % 2: return False
        if (mu[x]*u[x] + K(v) + lam[x]*v[x] - b0*lam[x] - b1*mu[x]) % 2: return False
    if a0 != b0: return False
    lu = sum(lam[p]*u[p] for p in S) % 2; mu_u = sum(mu[p]*u[p] for p in S) % 2
    lv = sum(lam[p]*v[p] for p in S) % 2
    return a1 == 0 and b1 == mu_u and lv == lu      # row (D) for c = 5
def primes_upto(n):
    return [q for q in range(3, n) if all(q % r for r in range(2, int(q**.5)+1))]
random.seed(7); P = primes_upto(60); ds = []
while len(ds) < 30:
    S = sorted(random.sample(P, random.randint(1, 4))); d = 1
    for q in S: d *= q
    if d % 8 == 5: ds.append((d, S))
mism = tot = 0
for d, S in ds:
    imgs = {p: image(d, p) for p in S + [2]}
    for a0, a1, b0, b1 in product((0, 1), repeat=4):
        for uu in product((0, 1), repeat=len(S)):
            for vv in product((0, 1), repeat=len(S)):
                u = dict(zip(S, uu)); v = dict(zip(S, vv))
                a = (-1)**a0 * 2**a1; b = (-1)**b0 * 2**b1
                for q in S: a *= q**u[q]; b *= q**v[q]
                loc = (a > 0) == (b > 0) and all((cls(a,p), cls(b,p)) in imgs[p] for p in imgs)
                tot += 1
                if loc != system(d, S, a0, a1, b0, b1, u, v): mism += 1
    print(d, S, "ok" if mism == 0 else mism)
print("pairs", tot, "mismatches", mism)
