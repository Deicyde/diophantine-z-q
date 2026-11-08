"""Is the TYZ certificate of a Selmer-minimal C_n determined by n mod 8 and the 2-adic/sign data
of one first coordinate a of the non-torsion Selmer coset?  For each sample n and each of the four
coset representatives (a, b), record key = (n mod 8, sign a, v2 a, |a|_odd mod 8) and the TYZ
outcome (any row of Smith's table for n mod 8 nonzero); report keys with conflicting outcomes.
Also report the same with (n mod 16) and with b's data added.  Usage: tyz_beta_rule.py N SEED
"""
import sys, random, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'rv-route-k'))
from sel2cong import selmer
import cypari2
from smith22_check import run

pari = cypari2.Pari()


def val(mask, gens):
    v = 1
    for i, g in enumerate(gens):
        if mask >> i & 1:
            v *= g
    return v


def two(x):
    v2 = 1 if x % 2 == 0 else 0
    return (1 if x < 0 else 0, v2, (abs(x) // (2 if v2 else 1)) % 8)


N = int(sys.argv[1]); rng = random.Random(int(sys.argv[2]))
tabs = {k: {} for k in ('a8', 'a16', 'ab8')}
rowcert = {k: {} for k in ('5a', '5b', '6', '7a', '7b')}
cnt = 0
tried = set()
sqf = lambda x: int(pari.core(x))
while cnt < N:
    if rng.random() < 0.5:
        n = rng.randrange(5, 10 ** 6)
    else:
        ps = rng.sample([int(p) for p in pari.primes(200)][1:], rng.randint(3, 7))
        n = 1
        for p in ps:
            n *= p
        if rng.random() < 0.4:
            n *= 2
    if n in tried or not pari.issquarefree(n) or n % 8 not in (5, 6, 7):
        continue
    tried.add(n)
    odd = [int(p) for p in pari.factor(n)[0] if int(p) != 2]
    basis, gens = selmer(n, odd)
    if len(basis) != 3:
        continue
    cnt += 1
    tors = [(1, 1), (n, 2), (-n, -2 * n), (-1, -n)]
    tset = {(sqf(a), sqf(b)) for a, b in tors}
    cls = [(sqf(val(a, gens)), sqf(val(b, gens))) for a, b in basis]
    sig = None
    for m in range(1, 8):
        A, B = 1, 1
        for j in range(3):
            if m >> j & 1:
                A *= cls[j][0]; B *= cls[j][1]
        if (sqf(A), sqf(B)) not in tset:
            sig = (sqf(A), sqf(B)); break
    coset = [(sqf(sig[0] * t[0]), sqf(sig[1] * t[1])) for t in tors]
    L, D, _, _, _ = run(n)
    cert = int(any(D.values()))
    for a, b in coset:
        for name, key in (('a8', (n % 8,) + two(a)), ('a16', (n % 16,) + two(a)),
                          ('ab8', (n % 8,) + two(a) + two(b))):
            tabs[name].setdefault(key, set()).add(cert)
        for r, v in D.items():
            rowcert[r].setdefault((n % 8,) + two(a), set()).add(v)
for name, t in tabs.items():
    conf = [k for k, v in t.items() if len(v) > 1]
    print(name, "keys", len(t), "conflicting", len(conf))
    if name == 'a8':
        for k in sorted(t):
            print("   n%8={} sgn={} v2={} |a|odd%8={} -> certificate {}".format(*k, sorted(t[k])))
for r, t in rowcert.items():
    conf = [k for k, v in t.items() if len(v) > 1]
    print("row", r, "a-only keys", len(t), "conflicting", len(conf))
