"""Differential test of Proposition N on 30 actual n = 5 (mod 8), n < 2e5, >= 3 primes:
T5a, T5b from Redei parities (own code) vs numerical analytic rank of C_n (PARI)."""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from genus import primes_of, g_redei_parity, set_partitions, prod
import cypari2
pari = cypari2.Pari(); pari.allocatemem(2 * 10**9)
rng = random.Random(1729)
seen, bad, nodd = set(), 0, 0
while len(seen) < 30:
    n = rng.randrange(5, 2 * 10**5, 8)
    if n in seen:
        continue
    try:
        ps = primes_of(n)
    except AssertionError:
        continue
    if len(ps) < 3:
        continue
    seen.add(n)
    g = {}
    T5a = T5b = 0
    for pi in set_partitions(ps):
        bl = [prod(B) for B in pi]; cl = sorted(b % 8 for b in bl); k = cl.count(1)
        w = 1
        for b in bl:
            g.setdefault(b, g_redei_parity(b)); w *= g[b]
        if cl.count(5) == 1 and k == len(cl) - 1: T5a += w
        if cl.count(7) == 1 and cl.count(3) == 1 and k == len(cl) - 2: T5b += w
    T5a %= 2; T5b %= 2
    ar = int(pari.ellanalyticrank(pari.ellinit([0, 0, 0, -n * n, 0]))[0])
    ok = not ((T5a or T5b) and ar != 1)
    bad += not ok; nodd += bool(T5a or T5b)
    print(n, ps, "T5a", T5a, "T5b", T5b, "an.rank", ar, "" if ok else "<-- CONTRADICTS Prop N", flush=True)
print("samples 30; with T5a or T5b odd:", nodd, "; contradictions:", bad)
