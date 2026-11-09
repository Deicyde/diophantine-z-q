"""Sanity check of reading A of Tian-Yuan-Zhang, Theorem 3.5(2), for n = 5 (mod 8).

Reading A: if L(n) = 0 then T5a and T5b are both even.  Equivalently: T5a odd or T5b odd
implies analytic rank exactly one.  For a sample of squarefree n = 5 (mod 8) with 2..6 odd primes below 100 and n < 300000,
compute T5a, T5b from PARI class groups and the analytic rank with ellanalyticrank; report any n
with T5a or T5b odd and analytic rank != 1 (a counterexample to reading A).
Usage: python reading_a_check.py COUNT SEED
"""
import random
import sys

import cypari2

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from literal_reading import sums  # noqa: E402

pari = cypari2.Pari()
pari.allocatemem(2 * 10**9)


def main():
    count, seed = int(sys.argv[1]), int(sys.argv[2])
    rnd = random.Random(seed)
    primes = [int(p) for p in pari.primes(25)[1:]]
    gcache = {}
    seen = 0
    stats = {}
    bad = []
    while seen < count:
        k = rnd.randint(2, 6)
        ps = sorted(rnd.sample(primes, k))
        n = 1
        for p in ps:
            n *= p
        if n % 8 != 5 or n > 300000:
            continue
        seen += 1
        T5a, T5b, _, _ = sums(n, ps, gcache)
        r = int(pari.ellanalyticrank(pari.ellinit([0, 0, 0, -n * n, 0]))[0])
        key = (T5a, T5b, r)
        stats[key] = stats.get(key, 0) + 1
        if (T5a or T5b) and r != 1:
            bad.append(n)
        print(f"n={n} primes={ps} T5a={T5a} T5b={T5b} analytic_rank={r}", flush=True)
    print("(T5a, T5b, rank) -> count:", dict(sorted(stats.items())))
    print("counterexamples to reading A:", bad)


if __name__ == "__main__":
    main()
