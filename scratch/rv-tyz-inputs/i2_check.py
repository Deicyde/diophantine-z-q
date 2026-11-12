"""I2 check (TYZ Lemma 2.8 with Prop. 2.3), numerically, for odd squarefree m = 1, 3 (mod 8).

For each sample m: compute calL(d) from L(E_d,1) for every divisor d of m with d = 1, 3 (mod 8)
(the only ones entering Lemma 2.8: d2 = 1 mod 8 and d1 = m/d2 = m mod 8), check that calL(d)^2 is
a perfect square of an integer (TYZ Thm 1.1 integrality), and check Lemma 2.8 modulo 2:

    sum over non-ordered m = d1*d2, d2 = 1 (mod 8), of calL(d1) calL(d2)  ==  g(m)   (mod 2)

(for m = 1 mod 8 each unordered pair {d1, d2} is counted once; for m = 3 the factor d2 = 1 is fixed by
its class). Also checks Theorem 1.1 in the set-partition form calL(m) = Lambda(m) (mod 2) (Lemma N1).
A wrong power of 2 in Thm 2.1 / Lemma 2.8 would break integrality or this congruence.
Usage: python i2_check.py m1 m2 ...
"""
import sys, time
from tyzcalc import pari, primes_of, divisors, g, calL2_rank0, nearest_square_root, set_partitions, prod

calL_cache = {1: 1}


def calL(d):
    if d not in calL_cache:
        v = calL2_rank0(d)
        r = nearest_square_root(v)
        if r is None:
            raise RuntimeError(f'calL({d})^2 = {v} is not a perfect square')
        calL_cache[d] = r
    return calL_cache[d]


def Lambda(m, gc):
    ps = primes_of(m) if m > 1 else []
    tot = 0
    for part in set_partitions(ps):
        blocks = [prod(b) for b in part]
        cls = [b % 8 for b in blocks]
        if m % 8 == 1 and any(c != 1 for c in cls):
            continue
        if m % 8 == 3 and sorted(c for c in cls if c != 1) != [3]:
            continue
        w = 1
        for b in blocks:
            if b not in gc:
                gc[b] = g(b)
            w &= gc[b]
        tot ^= w
    return tot


gc = {}
allok = True
for m in map(int, sys.argv[1:]):
    t0 = time.time()
    assert m % 2 == 1 and m % 8 in (1, 3) and pari.issquarefree(m)
    divs = [d for d in divisors(m) if d % 8 in (1, 3)]
    vals = {d: calL(d) for d in divs}
    # Lemma 2.8 sum
    s = 0
    pairs = []
    for d2 in divisors(m):
        if d2 % 8 != 1:
            continue
        d1 = m // d2
        if m % 8 == 1 and d1 < d2:
            continue          # unordered: count {d1, d2} once (d1 != d2 since m is squarefree, m > 1)
        pairs.append((d1, d2))
        s += vals[d1] * vals[d2]
    gm = g(m)
    lam = Lambda(m, gc)
    ok = (s - gm) % 2 == 0 and (vals[m] - lam) % 2 == 0
    allok &= ok
    print(f'm={m} = {"*".join(map(str, primes_of(m)))} (mod 8 = {m % 8}): calL(m)={vals[m]}, '
          f'#pairs={len(pairs)}, sum calL calL = {s} (mod 2 = {s % 2}), g(m)={gm}, Lambda(m)={lam}  '
          f'{"OK" if ok else "MISMATCH"}  ({time.time() - t0:.1f}s)', flush=True)
print('ALL OK' if allok else 'SOME MISMATCH')
print('calL values:', {d: v for d, v in sorted(calL_cache.items())})
