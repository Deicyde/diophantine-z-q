"""Exact check that the three points of certify_counterexamples.py are independent modulo
2C_n(Q) + torsion: their Kummer images (x, x - n) in (Q*/Q*^2)^2, together with those of the
torsion points (0,0) -> (-1, -n) and (n,0) -> (n, 2), are linearly independent over F_2.  Output: rank of the images."""
from fractions import Fraction
import cypari2
pari = cypari2.Pari()

def sqclass(q):
    q = Fraction(q)
    v = q.numerator * q.denominator
    s = -1 if v < 0 else 1
    core = int(pari.core(abs(v)))
    return s * core

def vec(a, b, primes):
    out = []
    for c in (a, b):
        out.append(1 if c < 0 else 0)
        out += [1 if c % p == 0 else 0 for p in primes]
    return out

def rank2(rows):
    rows = [r[:] for r in rows]; r = 0
    for c in range(len(rows[0])):
        piv = next((i for i in range(r, len(rows)) if rows[i][c]), None)
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i][c]: rows[i] = [(x + y) % 2 for x, y in zip(rows[i], rows[r])]
        r += 1
    return r

data = {26565: ["-18515", "-13860", "31740"], 33117: ["-20667", "-3616725/121", "-1120791/100"]}
for n, xs in data.items():
    primes = [2] + [int(p) for p in pari.factor(n)[0]]
    # torsion images (standard: T1=(0,0) -> (-1, -n)?) computed via the usual rule for x in {0, n}:
    # (n,0) -> (n, 2), (0,0) -> (-1, -n), using x(x-n)(x+n) = y^2 relations.
    tors = [(n, 2), (-1, -n)]
    rows = [vec(sqclass(a), sqclass(b), primes) for a, b in tors]
    for x in xs:
        X = Fraction(x)
        assert int(pari.issquare(pari(str(X * (X - n) * (X + n))))) == 1  # x is the abscissa of a rational point
        rows.append(vec(sqclass(X), sqclass(X - n), primes))
    print(n, "rank of Kummer images of torsion + 3 points:", rank2(rows), "(5 means rank >= 3)")
