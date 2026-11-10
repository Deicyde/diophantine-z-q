"""Lemma N1/N2 check on 30 actual n = 5 (mod 8), with g(d) from reduced forms (genus.g_forms)."""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from genus import primes_of, g_forms, prod
from coeff_recompute import run_config

rng = random.Random(7)
done, seen = 0, set()
tot = dict(n1_fail=0, n2_fail=0, nonreal=0, br_fail=0, ncoef=0)
odd = 0
while done < 30:
    n = rng.randrange(5, 3 * 10**6, 8)
    if n in seen:
        continue
    try:
        ps = primes_of(n)
    except AssertionError:
        continue
    if not (3 <= len(ps) <= 7):
        continue
    seen.add(n)
    r = len(ps)
    g = [1] + [g_forms(prod(ps[j] for j in range(r) if m >> j & 1)) % 2 for m in range(1, 1 << r)]
    o = run_config(r, [p % 8 for p in ps], g, check_readings=False)
    for k in tot:
        tot[k] += o[k]
    odd += o['T5b']
    done += 1
    print(n, ps, "T5a", o['T5a'], "T5b", o['T5b'], {k: o[k] for k in tot})
print("TOTAL", tot, "T5b odd in", odd)
