"""Driver: run a named family (at most 30 runs), print one line per run."""
import sys, random, time
from fractions import Fraction as Fr
import families
from construct import construct, summary
fam = sys.argv[1]; seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
rng = random.Random(seed)
import construct as _c
for a in sys.argv:
    if a.startswith("VARIANT="): _c.VARIANT = a.split("=")[1]
runs = getattr(families, fam)(rng)
assert len(runs) <= 30
nok = 0; t0 = time.time()
for i, (B, m, p0c, tag) in enumerate(runs):
    rec = construct(B, m, rng, p0c)
    print("#%02d %-14s %s" % (i, tag, summary(rec)), flush=True)
    if rec.get('ok'): nok += 1
    if '-v' in sys.argv: print("    B =", B)
print("family %s seed %d: %d/%d certified, %.0fs" % (fam, seed, nok, len(runs), time.time() - t0))
