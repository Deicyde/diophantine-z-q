"""Ground truth for Prop N (<= 30 inputs, sequential). For each n: primes, classes, T5a, T5b
(set-partition sums with g from PARI class groups; cross-checked against Rédei bits as in Lean),
analytic rank of y^2 = x^3 - n^2 x (ellanalyticrank), ellrank bounds.
Prop N: T5a or T5b odd => analytic rank 1;  analytic rank >= 3 => T5a = T5b = 0."""
import sys, time
sys.path.insert(0, 'scratch/rv-prop-n')
from tyzlib import *
ns = [int(x) for x in sys.argv[1].split(',')]
assert len(ns) <= 30
viol = 0
for n in ns:
    t0 = time.time()
    ps = primes_of(n); assert n % 8 == 5
    T5a, T5b = genus_sums(n)
    rd = genus_sums(n, True)
    ar = analytic_rank(n)
    rb = pari.ellrank(pari.ellinit([0, 0, 0, -n * n, 0]))
    pred = "rank1" if (T5a or T5b) else "-"
    bad = (pred == "rank1" and ar != 1) or (ar >= 2 and (T5a or T5b)) or rd != (T5a, T5b)
    viol += bad
    print(n, ps, [p % 8 for p in ps], "T5a", T5a, "T5b", T5b, "redei_ok", rd == (T5a, T5b),
          "an_rank", ar, "ellrank", (int(rb[0]), int(rb[1])), "pred", pred, "VIOLATION" if bad else "ok",
          "%.1fs" % (time.time() - t0), flush=True)
print("violations", viol)
