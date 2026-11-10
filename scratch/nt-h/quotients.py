"""For each rational u = a/b with M_S(u) = 1 (S = primes <= 13, |a|, b <= N; the list of
rs-height §3.3), and each of the 15 elliptic quotients E_I (|I| = 4) of the twist C_d through u,
decide whether the image of u in E_I^{(d)}(Q) is a torsion point.  If the image is non-torsion,
E_I^{(d)} has positive rank, so no rank-zero argument on that quotient can bound u.
Model: Y^2 = D prod_{c in I}(u - c), D = core(prod (a - c b)); send c4 to infinity by
s = 1/(u - c4), giving W^2 = D prod_{i<=3}(1 + k_i s), k_i = c4 - c_i; then X = K s with
K = D k1 k2 k3 gives y^2 = prod (X + K/k_i)."""
import sys
from fractions import Fraction as Fr
from itertools import combinations
from math import gcd, isqrt
import cypari2
pari = cypari2.Pari()
N = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
S = [2, 3, 5, 7, 11, 13]
C = [0, -15, -20, -24, -30, -60]
def sq_times_unit(x):
    x = abs(x)
    for p in S:
        while x % p == 0:
            x //= p
    r = isqrt(x)
    return r * r == x
pts = []
for b in range(1, N + 1):
    for a in range(-N, N + 1):
        if gcd(a, b) == 1 and all(a != c * b for c in C) and all(sq_times_unit(a - c * b) for c in C):
            pts.append((a, b))
print(len(pts), "points")
def core(n):
    return int(pari(f"core({n})"))
quads = list(combinations(C, 4))
tors_count = 0
nontors_all = 0
rows = []
for a, b in pts:
    u = Fr(a, b)
    ntor = 0
    for I in quads:
        c1, c2, c3, c4 = I
        prod = 1
        for c in I:
            prod *= (a - c * b)
        D = core(prod)
        k = [c4 - c1, c4 - c2, c4 - c3]
        K = D * k[0] * k[1] * k[2]
        s = 1 / (u - c4)
        X = K * s
        e = [Fr(K, ki) for ki in k]
        # y^2 = (X+e0)(X+e1)(X+e2) = X^3 + a2 X^2 + a4 X + a6
        a2 = e[0] + e[1] + e[2]
        a4 = e[0] * e[1] + e[0] * e[2] + e[1] * e[2]
        a6 = e[0] * e[1] * e[2]
        rhs = (X + e[0]) * (X + e[1]) * (X + e[2])
        num, den = rhs.numerator, rhs.denominator
        assert num >= 0 and isqrt(num) ** 2 == num and isqrt(den) ** 2 == den, (a, b, I)
        y = Fr(isqrt(num), isqrt(den))
        E = pari.ellinit([0, str(a2), 0, str(a4), str(a6)])
        P = [str(X), str(y)]
        assert int(pari.ellisoncurve(E, P)) == 1
        if int(pari.ellorder(E, P)) == 0:
            ntor += 1
    rows.append((a, b, ntor))
    if ntor == 15:
        nontors_all += 1
print("points whose image is non-torsion in all 15 quotients:", nontors_all)
hist = {}
for _, _, n in rows:
    hist[n] = hist.get(n, 0) + 1
print("histogram (#non-torsion quotients -> #points):", dict(sorted(hist.items())))
print("examples with fewer than 15:", [(a, b, n) for a, b, n in rows if n < 15][:20])
