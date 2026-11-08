"""Identify the kernel vector of Smith's unbordered block (M1 for n = 5, M2 for n = 6 mod 8) with
the non-torsion 2-Selmer class of a Selmer-minimal C_n.  For each coset representative (a, b)
(coordinates (x, x - n)), let S(c) be the indicator vector of the odd primes of n dividing c.
Test candidate identifications k = (S(u), S(w)) with u, w in {a, b, ab}, and report for how many
n some representative matches.  Usage: kernel_ident.py N SEED"""
import sys, os, random, itertools
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'rv-route-k'))
from sel2cong import selmer
from smith22_check import leg
import cypari2
pari = cypari2.Pari()
sqf = lambda x: int(pari.core(x))


def kernel_vecs(rows, n):
    # Gaussian elimination nullspace over F2; rows are ints over n columns
    piv = {}
    R = []
    for r in rows:
        for c, pr in piv.items():
            if r >> c & 1:
                r ^= pr
        if r:
            c = (r & -r).bit_length() - 1
            for c2 in list(piv):
                if piv[c2] >> c & 1:
                    piv[c2] ^= r
            piv[c] = r
    free = [c for c in range(n) if c not in piv]
    out = []
    for f in free:
        v = 1 << f
        for c, pr in piv.items():
            if pr >> f & 1:
                v |= 1 << c
        out.append(v)
    return out


N = int(sys.argv[1]); rng = random.Random(int(sys.argv[2]))
names = ['a', 'b', 'ab']
tally = {5: {}, 6: {}}
cnt = {5: 0, 6: 0}
tried = set()
while min(cnt.values()) < N:
    n = rng.randrange(5, 10 ** 6)
    t = n % 8
    if t not in (5, 6) or cnt[t] >= N or n in tried or not pari.issquarefree(n):
        continue
    tried.add(n)
    odd = [int(p) for p in pari.factor(n)[0] if int(p) != 2]
    r = len(odd)
    basis, gens = selmer(n, odd)
    if len(basis) != 3:
        continue
    A = [[leg(odd[j], odd[i]) if i != j else 0 for j in range(r)] for i in range(r)]
    for i in range(r):
        A[i][i] = sum(A[i]) % 2
    y = [leg(-1, p) for p in odd]; z = [leg(2, p) for p in odd]
    ex = [0] * r if t == 5 else [(a + b) % 2 for a, b in zip(y, z)]
    rows = []
    for i in range(r):
        row = [(A[i][j] + A[j][i] + (ex[i] if i == j else 0)) % 2 for j in range(r)] + [A[j][i] for j in range(r)]
        rows.append(sum(bb << c for c, bb in enumerate(row)))
    for i in range(r):
        row = A[i] + [z[i] if i == j else 0 for j in range(r)]
        rows.append(sum(bb << c for c, bb in enumerate(row)))
    ker = kernel_vecs(rows, 2 * r)
    if len(ker) != 1:
        continue
    cnt[t] += 1
    k = ker[0]
    def val(mask):
        v = 1
        for i, g in enumerate(gens):
            if mask >> i & 1:
                v *= g
        return v
    cls = [(sqf(val(a)), sqf(val(b))) for a, b in basis]
    tors = [(1, 1), (n, 2), (-n, -2 * n), (-1, -n)]
    tset = {(sqf(a), sqf(b)) for a, b in tors}
    sig = None
    for m in range(1, 8):
        a, b = 1, 1
        for j in range(3):
            if m >> j & 1:
                a *= cls[j][0]; b *= cls[j][1]
        if (sqf(a), sqf(b)) not in tset:
            sig = (sqf(a), sqf(b)); break
    reps = [(sqf(sig[0] * u), sqf(sig[1] * w)) for u, w in tors]
    S = lambda c: sum(1 << i for i, p in enumerate(odd) if c % p == 0)
    matched = []
    for u, w in itertools.product(range(3), repeat=2):
        ok = False
        for a, b in reps:
            vals = {'a': a, 'b': b, 'ab': sqf(a * b)}
            if S(vals[names[u]]) | (S(vals[names[w]]) << r) == k:
                ok = True
        key = (names[u], names[w])
        tally[t][key] = tally[t].get(key, 0) + ok
        if ok:
            matched.append(key)
    if os.environ.get('VERBOSE') and cnt[t] <= 12:
        print(n, n % 16, sorted(matched), 'k=', bin(k), 'reps', reps, 'primes', odd)
for t in (5, 6):
    print("n =", t, "mod 8, samples", cnt[t], ": k = (S(u), S(w)) matched by some representative:",
          {f"({u},{w})": c for (u, w), c in tally[t].items() if c})
