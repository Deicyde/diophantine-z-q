"""Selection only (not a ground-truth check): squarefree n ≡ 5 mod 8, >= 3 primes, random in range;
keep n whose PARI ellrank 2-descent upper bound is >= 3. Does NOT look at T5a/T5b."""
import sys, random, time
sys.path.insert(0, 'scratch/rv-prop-n')
from tyzlib import pari
rng = random.Random(int(sys.argv[1])); lo, hi, want, maxtry = map(int, sys.argv[2:6])
found = []; tries = 0; t0 = time.time()
while len(found) < want and tries < maxtry:
    n = rng.randrange(lo, hi) | 5
    n -= (n % 8) - 5
    if n % 8 != 5 or not pari.issquarefree(n) or int(pari.omega(n)) < 3: continue
    tries += 1
    E = pari.ellinit([0, 0, 0, -n * n, 0])
    r = pari.ellrank(E)
    if int(r[1]) >= 3:
        found.append((n, int(r[0]), int(r[1])))
print("tries", tries, "time %.0fs" % (time.time() - t0))
print(found)
