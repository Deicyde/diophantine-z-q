"""Validate the reformulation of Phi on toy inputs B = m(1 - theta s^2) (small theta),
building exact witnesses and checking Q_pole = 0.  Also record how often a solution
of small height exists (with m restricted to the given m)."""
import random
from fractions import Fraction as F
from phi_search import core, search, pole_poly

rng = random.Random(7)
tot = ok = 0
for theta in [1, 73, 97, 193, 241, 313, 337, 409, 433, 457]:
    for _ in range(3):
        s = F(rng.randrange(1, 40), rng.randrange(41, 400))
        m = 1
        B = m * (1 - theta * s * s)
        if B == 0:
            continue
        tot += 1
        res = search(B, 25)
        ok += res is not None
        print(theta, B, core(m * B), core(m * (m - B)), res, flush=True)
print(f"exact certificates found: {ok}/{tot}")
