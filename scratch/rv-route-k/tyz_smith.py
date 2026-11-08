"""Tian-Yuan-Zhang rank-one criterion in Smith's determinant form (arXiv:1603.08479, Table 2).

For squarefree n > 0 with odd part p_1...p_r: y_i = [-1/p_i]_+, z_i = [2/p_i]_+,
A_ij = [p_j/p_i]_+ (i != j), A_ii = sum_{j != i} A_ij, where [d/p]_+ = (1 - (d/p))/2 in F_2.
  M1 = |A+A^T, A^T; A, D_z|                      rk Sel_2 = 2 + corank(M1) for n = 1 (8)
  M2 = |A+A^T+D_{y+z}, A^T; A, D_z|              rk Sel_2 = 2 + corank(M2) for n = 2 (8)
  5a = |A+A^T, A^T, y+z; A, D_z, 0; (y+z)^T, 0, 0|
  5b = |A+A^T, A^T, 0; A, D_z, y; 0, y^T, 0|
  6  = |A+A^T+D_{y+z}, A^T, y; A, D_z, y; y^T, y^T, 0|
  7a = |A+A^T, A^T, y+z, 0; A, D_z, 0, y; (y+z)^T, 0, 0, 0; 0, y^T, 0, 0|
  7b = |A+A^T, A^T, y+z, y; A, D_z, 0, 0; (y+z)^T, 0, 0, 0; y^T, 0, 0, 0|
TYZ (Smith Thm 2.1/2.2): for n = 5, 6, 7 (8), det of the row's matrix nonzero => analytic rank 1.
The transcription is validated below against sel2cong (M1, M2 coranks; Selmer rank 3 whenever a
5/6/7 determinant is nonzero) and against PARI's analytic rank.
"""
import sys
import random
import cypari2
from sel2cong import selmer

pari = cypari2.Pari()
pari.allocatemem(10 ** 9)


def lp(a, p):
    a %= p
    return 0 if pow(a, (p - 1) // 2, p) == 1 else 1


def rank_f2(rows):
    rows = [r for r in rows]
    rk = 0
    ncols = max((r.bit_length() for r in rows), default=0)
    for c in range(ncols):
        piv = None
        for i in range(rk, len(rows)):
            if rows[i] >> c & 1:
                piv = i
                break
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        for i in range(len(rows)):
            if i != rk and rows[i] >> c & 1:
                rows[i] ^= rows[rk]
        rk += 1
    return rk


def build(blocks):
    """blocks: list of block-rows, each a list of matrices (lists of lists of 0/1). Returns bit rows."""
    rows = []
    for brow in blocks:
        h = len(brow[0])
        for i in range(h):
            bits = []
            for M in brow:
                bits.extend(M[i])
            v = 0
            for j, b in enumerate(bits):
                if b:
                    v |= 1 << j
            rows.append(v)
    return rows


def data(n):
    ps = [int(p) for p in pari.factor(n)[0] if int(p) != 2]
    r = len(ps)
    A = [[0] * r for _ in range(r)]
    for i in range(r):
        for j in range(r):
            if i != j:
                A[i][j] = lp(ps[j], ps[i])
        A[i][i] = sum(A[i][j] for j in range(r) if j != i) % 2
    y = [lp(-1, p) for p in ps]
    z = [lp(2, p) for p in ps]
    return ps, A, y, z


def mats(n):
    ps, A, y, z = data(n)
    r = len(ps)
    T = [[A[j][i] for j in range(r)] for i in range(r)]
    ApT = [[(A[i][j] + T[i][j]) % 2 for j in range(r)] for i in range(r)]
    Dz = [[z[i] if i == j else 0 for j in range(r)] for i in range(r)]
    Dyz = [[(y[i] + z[i]) % 2 if i == j else 0 for j in range(r)] for i in range(r)]
    ApTyz = [[(ApT[i][j] + Dyz[i][j]) % 2 for j in range(r)] for i in range(r)]
    col = lambda v: [[x] for x in v]
    row = lambda v: [list(v)]
    Z = lambda a, b: [[0] * b for _ in range(a)]
    yz = [(a + b) % 2 for a, b in zip(y, z)]
    out = {}
    out["1"] = (build([[ApT, T], [A, Dz]]), 2 * r)
    out["2"] = (build([[ApTyz, T], [A, Dz]]), 2 * r)
    out["5a"] = (build([[ApT, T, col(yz)], [A, Dz, Z(r, 1)], [row(yz), Z(1, r), Z(1, 1)]]), 2 * r + 1)
    out["5b"] = (build([[ApT, T, Z(r, 1)], [A, Dz, col(y)], [Z(1, r), row(y), Z(1, 1)]]), 2 * r + 1)
    out["6"] = (build([[ApTyz, T, col(y)], [A, Dz, col(y)], [row(y), row(y), Z(1, 1)]]), 2 * r + 1)
    out["7a"] = (build([[ApT, T, col(yz), Z(r, 1)], [A, Dz, Z(r, 1), col(y)],
                        [row(yz), Z(1, r), Z(1, 1), Z(1, 1)], [Z(1, r), row(y), Z(1, 1), Z(1, 1)]]), 2 * r + 2)
    out["7b"] = (build([[ApT, T, col(yz), col(y)], [A, Dz, Z(r, 1), Z(r, 1)],
                        [row(yz), Z(1, r), Z(1, 1), Z(1, 1)], [row(y), Z(1, r), Z(1, 1), Z(1, 1)]]), 2 * r + 2)
    return out


def tyz(n):
    """True if Tian-Yuan-Zhang's criterion (Smith's determinant form) certifies analytic rank 1."""
    n = abs(n)
    M = mats(n)
    t = n % 8
    rows = {5: ["5a", "5b"], 6: ["6"], 7: ["7a", "7b"]}.get(t, [])
    return any(rank_f2(M[k][0]) == M[k][1] for k in rows)


def oddprimes(n):
    return [int(p) for p in pari.factor(abs(n))[0] if int(p) != 2]


if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    bad = 0
    cnt = {"1": 0, "2": 0, "tyz": 0, "tyz_an": 0, "S3": 0}
    tested = set()
    while cnt["1"] + cnt["2"] < 60 or cnt["S3"] < 60:
        n = rng.randrange(3, 10 ** 6)
        if n in tested or int(pari.issquarefree(n)) == 0:
            continue
        tested.add(n)
        sel = len(selmer(n, oddprimes(n))[0])
        M = mats(n)
        t = n % 8
        if t in (1, 2):
            k = str(t)
            cor = M[k][1] - rank_f2(M[k][0])
            if 2 + cor != sel:
                bad += 1
                print("MISMATCH corank", n, t, sel, cor)
            cnt[k] += 1
        elif t in (5, 6, 7):
            T = tyz(n)
            if sel == 3:
                cnt["S3"] += 1
            if T:
                cnt["tyz"] += 1
                if sel != 3:
                    bad += 1
                    print("TYZ but Selmer rank", sel, n)
                if n < 3 * 10 ** 4 and cnt["tyz_an"] < 25:
                    E = pari.ellinit([0, 0, 0, -n * n, 0])
                    ar = int(pari.ellanalyticrank(E)[0])
                    cnt["tyz_an"] += 1
                    if ar != 1:
                        bad += 1
                        print("TYZ but analytic rank", ar, n)
    print(cnt, "mismatches", bad)
    print("fraction of Selmer-rank-3 n (t = 5,6,7) with TYZ:", cnt["tyz"], "/", cnt["S3"])
