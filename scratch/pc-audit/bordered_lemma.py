"""(1) Bordered-determinant lemma over F_2: for symmetric M of corank one with kernel vector k,
det [[M, v], [v^T, 0]] = v.k.  Checked on random matrices.
(2) Corank of Smith's unbordered blocks M1 = [[A+A^T, A^T], [A, D_z]] and
M2 = [[A+A^T+D_{y+z}, A^T], [A, D_z]] against dim Sel_2(C_n) - 2 for n = 5, 6, 7 (mod 8).
Usage: bordered_lemma.py NRANDOMMATRICES NSEL SEED"""
import sys, random, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'rv-route-k'))
from smith22_check import det2, leg
from sel2cong import selmer
import cypari2
pari = cypari2.Pari()


def rank2(rows, ncols):
    rows = list(rows); rk = 0
    for c in range(ncols):
        piv = next((i for i in range(rk, len(rows)) if rows[i] >> c & 1), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        for i in range(len(rows)):
            if i != rk and rows[i] >> c & 1:
                rows[i] ^= rows[rk]
        rk += 1
    return rk


def kernel(rows, n):
    # brute force for small n
    out = []
    for x in range(1, 1 << n):
        if all(bin(r & x).count('1') % 2 == 0 for r in rows):
            out.append(x)
    return out


NR, NS, seed = map(int, sys.argv[1:4])
rng = random.Random(seed)
ok = tested = 0
while tested < NR:
    n = rng.randint(2, 9)
    M = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i, n):
            M[i][j] = M[j][i] = rng.randint(0, 1)
    rows = [sum(M[i][j] << j for j in range(n)) for i in range(n)]
    if rank2(rows, n) != n - 1:
        continue
    k = kernel(rows, n)[0]
    v = rng.randrange(1 << n)
    big = [rows[i] | ((v >> i & 1) << n) for i in range(n)] + [v]
    tested += 1
    ok += det2(big, n + 1) == bin(v & k).count('1') % 2
print("bordered lemma: agreements", ok, "of", tested)

stats = {}
cnt = 0
while cnt < NS:
    n = rng.randrange(5, 10 ** 6)
    if not pari.issquarefree(n) or n % 8 not in (5, 6, 7):
        continue
    cnt += 1
    odd = [int(p) for p in pari.factor(n)[0] if int(p) != 2]
    r = len(odd)
    sel = len(selmer(n, odd)[0])
    A = [[leg(odd[j], odd[i]) if i != j else 0 for j in range(r)] for i in range(r)]
    for i in range(r):
        A[i][i] = sum(A[i]) % 2
    y = [leg(-1, p) for p in odd]; z = [leg(2, p) for p in odd]
    def blk(extra):
        rows = []
        for i in range(r):
            row = [(A[i][j] + A[j][i] + (extra[i] if i == j else 0)) % 2 for j in range(r)] + [A[j][i] for j in range(r)]
            rows.append(sum(b << c for c, b in enumerate(row)))
        for i in range(r):
            row = A[i] + [z[i] if i == j else 0 for j in range(r)]
            rows.append(sum(b << c for c, b in enumerate(row)))
        return 2 * r - rank2(rows, 2 * r)
    c1 = blk([0] * r); c2 = blk([(a + b) % 2 for a, b in zip(y, z)])
    key = (n % 8, sel - 2, c1, c2)
    stats[key] = stats.get(key, 0) + 1
print("(n mod 8, dim Sel2 - 2, corank M1 block, corank M2 block): count")
for k in sorted(stats):
    print(" ", k, stats[k])
