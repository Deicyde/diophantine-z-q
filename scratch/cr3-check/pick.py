"""Pick the test set of d: squarefree, d = 5 (mod 8), 2..5 odd prime factors, primes < 200."""
import random, json
from sympy import primerange
from sel2_indep import first_coords
rng = random.Random(20261109)
P = list(primerange(3, 200))
pool = {}
while len(pool) < 400:
    k = rng.choice([2, 3, 4, 5])
    ps = sorted(rng.sample(P, k))
    d = 1
    for p in ps: d *= p
    if d % 8 != 5 or d in pool: continue
    pool[d] = ps
hyp, other = [], []
for d, ps in pool.items():
    dim, firsts = first_coords(d, ps)
    good = dim == 3 and any(abs(a) % 8 == 7 for a in firsts)
    (hyp if good else other).append((d, ps))
print(len(hyp), len(other))
chosen = []
for k in (2, 3, 4, 5):
    chosen += [x for x in hyp if len(x[1]) == k][:6]
    chosen += [x for x in other if len(x[1]) == k][:4]
classes = {p % 8 for d, ps in chosen for p in ps}
print(len(chosen), sorted(classes))
json.dump(chosen, open('dset.json', 'w'))
print(' '.join(str(d) for d, ps in chosen))
