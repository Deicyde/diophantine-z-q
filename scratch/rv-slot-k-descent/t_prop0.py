"""Differential check: Proposition 0 (prop0.py) against the point-based descent (sel2.py).
30 random odd squarefree d (all four classes mod 8), compare dim Sel_2 and pi_1 membership of
every squarefree divisor of +-d. Optionally (ELLRANK=1) compare with PARI ellrank on the first 10."""
import os
import random
from itertools import combinations

from sel2 import selmer, first_coord_contains, Span
from prop0 import prop0_selmer

SMALLP = [p for p in range(3, 400) if all(p % q for q in range(2, int(p ** 0.5) + 1))]


def main():
    rng = random.Random(20261108)
    cases = []
    want = [1, 3, 5, 7] * 8
    for c in want[:30]:
        while True:
            k = rng.randrange(1, 6)
            ps = sorted(rng.sample(SMALLP, k))
            d = 1
            for p in ps:
                d *= p
            if d % 8 == c:
                cases.append((d, ps)); break
    pari = None
    if os.environ.get("ELLRANK"):
        import cypari2
        pari = cypari2.Pari()
    mism = 0
    for idx, (d, ps) in enumerate(cases):
        g1, k1 = selmer(d, ps, seed=idx)
        g2, k2 = prop0_selmer(d, ps)
        s1, s2 = Span(), Span()
        for x in k1: s1.add(x)
        for x in k2: s2.add(x)
        same = s1.dim() == s2.dim() and all(s1.reduce(x) == 0 for x in k2)
        divs_ok = True
        for r in range(len(ps) + 1):
            for sub in combinations(ps, r):
                a = 1
                for p in sub: a *= p
                for sgn in (1, -1):
                    if first_coord_contains(g1, k1, sgn * a) != first_coord_contains(g2, k2, sgn * a):
                        divs_ok = False
        line = "d=%d (%d mod 8) primes=%s dim(points)=%d dim(prop0)=%d same_space=%s pi1_agree=%s" % (
            d, d % 8, ps, s1.dim(), s2.dim(), same, divs_ok)
        if pari is not None and idx < 10:
            E = pari.ellinit([0, 0, 0, -d * d, 0])
            r = pari.ellrank(E)
            line += " ellrank=%s" % (r[:3],)
        if not (same and divs_ok):
            mism += 1
        print(line, flush=True)
    print("mismatches:", mism, "of", len(cases))


if __name__ == "__main__":
    main()
