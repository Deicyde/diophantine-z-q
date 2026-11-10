"""Test the readings of the second sum of Tian-Yuan-Zhang, Theorem 1.2, for n = 5 (mod 8).

For squarefree n = 5 (mod 8) with analytic rank >= 3 (so L(n) = 0 and 2^{-rho} L(n) is even),
the theorem asserts that the first sum and the second sum are both even.  We compute, with
g(d) from PARI class groups:

  T5a  = sum over partitions of the primes of n into one block of class 5 and blocks of class 1
  T5b  = sum over partitions into one block of class 7, one of class 3, and blocks of class 1
  S51_unord = (5,1) terms with d_1 > 1, decompositions unordered (d_1 not distinguished
              from the other class-1 factors): partitions with a class-5 block and >= 1 class-1 block
  S51_dist  = (5,1) terms with d_1 > 1 distinguished: sum of k * prod g, k = number of class-1 blocks

Readings of the second sum:
  A (d_1 = 1 admitted, as in the proof)   : T5a + T5b
  B (d_1 > 1, unordered)                  : S51_unord + T5b
  C (d_1 > 1, d_1 distinguished)          : S51_dist + T5b
The theorem under reading X is refuted by any rank->=3 n where the reading-X sum is odd.

Usage: python literal_reading.py NMAX [MAXPRIMES]
"""
import sys
from itertools import combinations

import cypari2

pari = cypari2.Pari()
pari.allocatemem(2 * 10**9)


def gpar(d):
    """g(d) mod 2: 1 iff Cl(Q(sqrt(-d))) has no element of order 4."""
    D = -d if d % 4 == 3 else -4 * d
    cyc = [int(c) for c in pari.quadclassunit(D)[1]]
    return 0 if any(c % 4 == 0 for c in cyc) else 1


def partitions(items):
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for k in range(len(rest) + 1):
        for comb in combinations(rest, k):
            block = (first,) + comb
            remaining = [x for x in rest if x not in comb]
            for p in partitions(remaining):
                yield [block] + p


def prod(xs):
    r = 1
    for x in xs:
        r *= x
    return r


def sums(n, primes, gcache):
    def g(block):
        d = prod(block)
        if d not in gcache:
            gcache[d] = gpar(d)
        return gcache[d]

    T5a = T5b = S51u = S51d = 0
    for pi in partitions(primes):
        cls = [prod(b) % 8 for b in pi]
        c1 = cls.count(1)
        others = sorted(c for c in cls if c != 1)
        if others == [5]:
            w = prod(g(b) for b in pi)
            T5a += w
            if c1 >= 1:
                S51u += w
                S51d += c1 * w
        elif others == [3, 7]:
            T5b += prod(g(b) for b in pi)
    return T5a % 2, T5b % 2, S51u % 2, S51d % 2


def main():
    nmax = int(sys.argv[1])
    maxp = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    gcache = {}
    counts = {"A": 0, "B": 0, "C": 0}
    nrank3 = 0
    for n in range(5, nmax + 1, 8):
        f = pari.factor(n)
        exps = [int(e) for e in f[1]]
        if any(e > 1 for e in exps):
            continue
        primes = [int(p) for p in f[0]]
        if len(primes) > maxp:
            continue
        E = pari.ellinit([0, 0, 0, -n * n, 0])
        r = int(pari.ellanalyticrank(E)[0])
        if r < 3:
            continue
        nrank3 += 1
        T5a, T5b, S51u, S51d = sums(n, primes, gcache)
        A = (T5a + T5b) % 2
        B = (S51u + T5b) % 2
        C = (S51d + T5b) % 2
        for k, v in (("A", A), ("B", B), ("C", C)):
            counts[k] += v
        print(f"n={n} primes={primes} rank={r} g(n)={gcache.get(n, gpar(n))} "
              f"T5a={T5a} T5b={T5b} secondA={A} secondB={B} secondC={C}", flush=True)
    print(f"rank>=3 curves: {nrank3}; reading refuted on (count of odd second sums): {counts}")


if __name__ == "__main__":
    main()
