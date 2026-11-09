"""Section 1.4 counterexamples: factorisation, g(d) on all divisors, genus sums under readings A-D.

Run: python -I counterexamples.py  (needs cypari2 only for the comparison column).
"""
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from itertools import combinations
from genus import primes_of, g_forms, g_redei_parity, set_partitions, prod, disc

try:
    import cypari2
    pari = cypari2.Pari()
except ImportError:
    pari = None


def analyse(n):
    ps = primes_of(n)
    assert prod(ps) == n and n % 8 == 5
    print(f"n = {n} = {'*'.join(map(str, ps))}, n mod 8 = {n % 8}, classes {[p % 8 for p in ps]}")
    if pari is not None:
        print("  PARI factor:", pari.factor(n))
    g = {}
    for r in range(1, len(ps) + 1):
        for S in combinations(ps, r):
            d = prod(S)
            gf = g_forms(d)
            gr = g_redei_parity(d)
            assert gf % 2 == gr, (d, gf, gr)
            if pari is not None:
                D = disc(d)
                h = int(pari.qfbclassno(D))
                cyc = [int(c) for c in pari.quadclassunit(D)[1]]
                g_p = h // (2 ** sum(1 for c in cyc if c % 2 == 0))
                assert g_p == gf, (d, g_p, gf)
            g[d] = gf
    print("  g(d) mod 2 (agreeing: forms, Redei, PARI):",
          {d: g[d] % 2 for d in sorted(g)})
    T5a = T5b = sB = sC = sD = 0
    for pi in set_partitions(ps):
        blocks = [prod(B) for B in pi]
        cls = sorted(b % 8 for b in blocks)
        w = prod(g[b] % 2 for b in blocks)
        k1 = cls.count(1)
        if cls.count(5) == 1 and k1 == len(cls) - 1:
            T5a += w
            sC += k1 * w
            sD += (1 + k1) * w
            if k1 >= 1:
                sB += w
        if cls.count(7) == 1 and cls.count(3) == 1 and k1 == len(cls) - 2:
            T5b += w
    res = dict(g_n=g[n] % 2, T5a=T5a % 2, T5b=T5b % 2,
               second_A=(T5a + T5b) % 2, second_B=(sB + T5b) % 2,
               second_C=(sC + T5b) % 2, second_D=(sD + T5b) % 2)
    print("  ", res)
    return res


if __name__ == "__main__":
    for n in (26565, 33117):
        analyse(n)
