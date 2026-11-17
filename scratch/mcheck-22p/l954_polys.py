"""mcheck-22p step 4 (tex L948-954): coefficient data of P(X) = -57600 b F(X)^2 - a G(X)^6,
F = X(X+15)(X+20)(X+24)(X+30)(X+60), G = 7X^2+300X+3600, and the quotients used in L954.lean."""
from collections import defaultdict
def mul(f, g):
    h = defaultdict(int)
    for (i, j), c in f.items():
        for (k, l), d in g.items():
            h[(i + k, j + l)] += c * d
    return {k: v for k, v in h.items() if v}
def add(f, g, s=1):
    h = defaultdict(int, f)
    for k, v in g.items(): h[k] += s * v
    return {k: v for k, v in h.items() if v}
def pw(f, n):
    r = {(0, 0): 1}
    for _ in range(n): r = mul(r, f)
    return r
p, q = {(1, 0): 1}, {(0, 1): 1}
def lin(c): return {(1, 0): 1, (0, 1): c}
F = {(0, 0): 1}
for c in (0, 15, 20, 24, 30, 60): F = mul(F, lin(c))
G = {(2, 0): 7, (1, 1): 300, (0, 2): 3600}
F2, G6 = pw(F, 2), pw(G, 6)
l1F2 = sum(abs(v) for v in F2.values()); l1G6 = sum(abs(v) for v in G6.values())
print("F(1) =", sum(F.values()), " l1(57600 F^2) =", 57600 * l1F2, " l1(G^6) =", l1G6)
print("2*4000^6 =", 2 * 4000 ** 6, " 57600*l1(F^2)+l1(G^6) <= 2*4000^6:", 57600 * l1F2 + l1G6 <= 2 * 4000 ** 6)
print("max coefficient of 57600F^2:", 57600 * max(F2.values()), " of G^6:", max(G6.values()))
print("constant term of G^6 = 3600^6 =", 3600 ** 6, "; leading terms 57600 and 7^6 =", 7 ** 6)
import math
print("log(2*4000^6) =", math.log(2 * 4000 ** 6))
def show(f):
    return " + ".join(f"({c}) * p^{i} * q^{j}" for (i, j), c in sorted(f.items(), reverse=True))
G3 = pw(G, 3)
for sgn, name in ((-1, "G^3 - 343 F"), (1, "G^3 + 343 F")):
    D = add(G3, {k: 343 * v for k, v in F.items()}, sgn)
    print(name, "=", show(D))
    lead = {k: v for k, v in D.items() if k[1] <= 1}
    rest = {(i, j - 2): v for (i, j), v in D.items() if j >= 2}
    print("  terms with q-degree <= 1:", lead)
    print("  quotient by q^2 of the rest:", show(rest))
