"""Batch 4: the sign step of Prop AP around the change of case (A' + 60 = 1, i.e. A = -69) and at
the A where S+ has coincidences.  For each A: max S+, the case, and for random x, v >= 1:
F(t1) > 0, F(t2) > 0, t2 < -60, t1 > max S+.  30 values of A; 200 random (x, v) each."""
import random
from fractions import Fraction as Fr
from ap_search import splus
import slopelib as L
rng = random.Random(3)
As = list(range(-75, -62)) + [-130, -71 - 59, -55, -50, -45, -40, -35, -30, -10, 0, 1, 50, 10**6, -10**6, -121, -120, -70 + 0][:17]
As = sorted(set(As))[:30]
bad = []
for A in As:
    S = splus(A); Ap = A + 10
    case = 1 if Ap + 60 >= 1 else 2
    ok = True
    for _ in range(200):
        v = rng.choice([1, 2, 3, 2**40, 3**30 * 7, rng.randint(1, 10**9)])
        x = rng.choice([1, rng.randint(1, 10**12), v * 10**6 + 1])
        u = x + max(S) * v
        t1 = Fr(u, v); t2 = Ap - t1
        if t1 in [Fr(c) for c in L.CSET + [1]] or t2 in [Fr(c) for c in L.CSET + [1]]:
            ok = False; break
        if not (L.F(t1) > 0 and L.F(t2) > 0 and t2 < -60 and t1 > max(S)):
            ok = False; break
    print(f"A={A:9d} |S+|={len(S):2d} max S+={max(S):8d} case={case} signs ok={ok}")
    if not ok:
        bad.append(A)
print("failures:", bad)
