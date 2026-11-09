import time, random, real_dl as R
rng = random.Random(1)
t = time.time()
B, m = R.fam_random(rng); print('gen', time.time() - t, B, m, flush=True)
beta, P = R.sqf(m * B); theta, T = R.sqf(m * (m - B)); print(beta, P, T, time.time() - t, flush=True)
q0, RP, RT = R.construct(rng, beta, P, T)
print('constructed', time.time() - t, [len(str(a)) for a in [q0] + RP + RT], flush=True)
aux = [q0] + RP + RT
n = abs(beta)
for r in aux:
    n *= r
print(R.certify(n, P + aux, beta), time.time() - t, flush=True)
print(R.certify(n * theta, P + aux + T, beta), time.time() - t, flush=True)
