"""Selection only: n = product of k random primes among the first pb primes (odd), n ≡ 5 mod 8,
>= 1 prime ≡ 7 and >= 1 prime ≡ 3 mod 8 (so T5b has terms), n < hi; keep ellrank upper bound >= 3.
Does NOT look at T5a/T5b."""
import sys, random, time
sys.path.insert(0, 'scratch/rv-prop-n')
from tyzlib import pari, prod
rng = random.Random(int(sys.argv[1])); k, pb, hi, want, maxtry = map(int, sys.argv[2:7])
smallp = [int(p) for p in pari.primes(pb)][1:]
found = set(); tries = 0; t0 = time.time()
while len(found) < want and tries < maxtry:
    ps = sorted(rng.sample(smallp, k)); n = prod(ps)
    if n % 8 != 5 or n > hi or not any(p % 8 == 7 for p in ps) or not any(p % 8 == 3 for p in ps): continue
    if n in found: continue
    tries += 1
    r = pari.ellrank(pari.ellinit([0, 0, 0, -n * n, 0]))
    if int(r[1]) >= 3: found.add(n)
print("k", k, "tries", tries, "time %.0fs" % (time.time() - t0), sorted(found))
