import time, random, sys
sys.argv = ["x", "none"]
import run_dl, slotk
rng = random.Random(5)
B = run_dl.gen_random(rng)
t = time.time()
ms = slotk.choose_m(B, run_dl.fac); print("m", ms[:3], time.time() - t, flush=True)
m = ms[0]
beta = slotk.sqf(m * B, run_dl.fac); theta = slotk.sqf(m * (m - B), run_dl.fac)
P = sorted(run_dl.fac(beta)); T = sorted(run_dl.fac(theta)); print(P, T, time.time() - t, flush=True)
q0, RP, RT = slotk.construct(beta, theta, P, T); print("constructed", time.time() - t, [len(str(a)) for a in [q0] + RP + RT], flush=True)
from math import prod
aux = [q0] + RP + RT; n = beta * prod(aux)
print(slotk.certified(n, P + aux, beta), time.time() - t, flush=True)
print(slotk.certified(n * theta, P + aux + T, beta), time.time() - t, flush=True)
