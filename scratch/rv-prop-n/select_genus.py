"""Selection only: squarefree n ≡ 5 mod 8 with k primes (random), at least two primes ≡ 3 mod 8 and one
≡ 7 mod 8 (so chains with >= 2 class-3 steps, i.e. (5,3) epsilon-steps, occur); report T5a, T5b."""
import sys, random
sys.path.insert(0, 'scratch/rv-prop-n')
from tyzlib import *
rng = random.Random(int(sys.argv[1])); k = int(sys.argv[2]); hi = int(sys.argv[3]); want = int(sys.argv[4]); pb = int(sys.argv[5])
smallp = [int(p) for p in pari.primes(pb)][1:]
out = {}
tries = 0
while sum(len(v) for v in out.values()) < want and tries < 4000:
    tries += 1
    ps = sorted(rng.sample(smallp, k))
    n = prod(ps)
    if n % 8 != 5 or n > hi: continue
    if sum(p % 8 == 3 for p in ps) < 2 or sum(p % 8 == 7 for p in ps) < 1: continue
    t = genus_sums(n)
    assert t == genus_sums(n, True), n
    out.setdefault(t, [])
    if len(out[t]) < want // 2: out[t].append(n)
print(out)
