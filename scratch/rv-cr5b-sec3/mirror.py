"""rv-cr5b-sec3: Python mirror of the Lean definitions behind CertifiedRankTYZ, and a red team.

Mirrors (ZInQKernel/RouteK/...):
  legBit p a      = 0 if IsSquare (a : ZMod p) else 1      (Slots/Symbols.lean; 0 counts as a square)
  aBit d i j      = legBit p_i p_j ; yBit = legBit p (-1) ; zBit = legBit p 2   (Rank5b/Matrices.lean)
  Sec3.lapl a U   : L_ij = a_ij (i != j), L_ii = sum_{k in U, k != i} a_ik      (Sec3/Defs.lean)
  Sec3.kappa a B r = det (lapl a B) restricted to B \\ {r}
  Sec3.redeiG     = sum_{r in B} y_r kappa_r(B) if y(B) = 1 else sum_{r in B} z_r kappa_r(B)
  Admissible5bNat : exactly one block with dProd = 7 mod 8, exactly one = 3, all blocks in {7,3,1}
  T5b d           = sum over set partitions of the primes of d of [Admissible5bNat] prod gBit
  Sec3.genusSum5b : same, classes read off (y(B), z(B))
  M5b d           = border (fromBlocks (L+L^T) L^T L (diag z)) (Sum.elim 0 y)  (Bordered.lean `border`)
  Sel2 d          = pairs of squarefree integers (a, b) with Loc R and Loc Q_p for all p
                    (Selmer/Covering.lean); computed here through the local Kummer images of C_d(Q_v)
                    (Lean: loc_iff_kummer), restricted to the support {-1, 2, p | d} (Lean: Prop0,
                    Sel2 d subset range selPair).
Independent sources (PARI via cypari2): quadclassunit for g(d_B) (Redei's formula, Prop 2.3),
ellrank / ellanalyticrank and explicit points for the conclusion `Loc Q d a b`.

Run: python3 -I mirror.py   (inside a venv with cypari2)
"""
import itertools
import sys

import cypari2

pari = cypari2.Pari()
pari.allocatemem(2 * 10**9)


# ---------------------------------------------------------------- bits and F2 linear algebra
def leg_bit(p, a):
    a %= p
    if a == 0:
        return 0  # IsSquare 0
    return 0 if pow(a, (p - 1) // 2, p) == 1 else 1


def det2(M):
    """Determinant over F2 of a square list-of-lists matrix (0x0 -> 1)."""
    n = len(M)
    A = [row[:] for row in M]
    for c in range(n):
        piv = next((r for r in range(c, n) if A[r][c] & 1), None)
        if piv is None:
            return 0
        A[c], A[piv] = A[piv], A[c]
        for r in range(c + 1, n):
            if A[r][c] & 1:
                A[r] = [(x ^ y) & 1 for x, y in zip(A[r], A[c])]
    return 1


def primes_of(d):
    return [int(p) for p in pari.factor(d)[0]]


class Bits:
    def __init__(self, d):
        self.d = d
        self.P = primes_of(d)
        r = len(self.P)
        self.r = r
        self.a = [[leg_bit(self.P[i], self.P[j]) for j in range(r)] for i in range(r)]
        self.y = [leg_bit(p, -1) for p in self.P]
        self.z = [leg_bit(p, 2) for p in self.P]

    def lapl_entry(self, U, i, j):
        if i == j:
            return sum(self.a[i][k] for k in U if k != i) % 2
        return self.a[i][j]

    def kappa(self, B, rho):
        idx = [i for i in B if i != rho]
        return det2([[self.lapl_entry(B, i, j) for j in idx] for i in idx])

    def redeiG(self, B):
        yB = sum(self.y[i] for i in B) % 2
        w = self.y if yB == 1 else self.z
        return sum(w[r] * self.kappa(B, r) for r in B) % 2

    def dprod(self, B):
        out = 1
        for i in B:
            out *= self.P[i]
        return out

    def cls_bits(self, B):
        yB = sum(self.y[i] for i in B) % 2
        zB = sum(self.z[i] for i in B) % 2
        return {(0, 0): 1, (0, 1): 5, (1, 0): 7, (1, 1): 3}[(yB, zB)]


def set_partitions(items):
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for part in set_partitions(rest):
        yield [[first]] + part
        for k in range(len(part)):
            yield part[:k] + [[first] + part[k]] + part[k + 1:]


def T5b(bits):
    """Lean T5b: residues of d_B mod 8."""
    tot = 0
    nadm = 0
    for part in set_partitions(list(range(bits.r))):
        cl = [bits.dprod(B) % 8 for B in part]
        if cl.count(7) == 1 and cl.count(3) == 1 and all(c in (7, 3, 1) for c in cl):
            nadm += 1
            prod = 1
            for B in part:
                prod *= bits.redeiG(B)
            tot += prod
    return tot % 2, nadm


def genusSum5b(bits):
    """Lean Sec3.genusSum5b: classes read off the bits."""
    tot = 0
    for part in set_partitions(list(range(bits.r))):
        cl = [bits.cls_bits(B) for B in part]
        if cl.count(7) == 1 and cl.count(3) == 1 and 5 not in cl:
            prod = 1
            for B in part:
                prod *= bits.redeiG(B)
            tot += prod
    return tot % 2


def detM5b(bits):
    r = bits.r
    L = [[bits.lapl_entry(range(r), i, j) for j in range(r)] for i in range(r)]
    n = 2 * r + 1
    M = [[0] * n for _ in range(n)]
    for i in range(r):
        for j in range(r):
            M[i][j] = (L[i][j] + L[j][i]) % 2      # L + L^T
            M[i][r + j] = L[j][i]                   # L^T
            M[r + i][j] = L[i][j]                   # L
        M[r + i][r + i] = bits.z[i]                 # diag z
        M[r + i][2 * r] = bits.y[i]                 # border column (0, y)
        M[2 * r][r + i] = bits.y[i]                 # border row
    return det2(M)


def g_pari(m):
    """g(m) = #2Cl(Q(sqrt(-m))) mod 2: 1 iff no cyclic factor of Cl has order divisible by 4."""
    D = -m if m % 4 == 3 else -4 * m
    cyc = [int(c) for c in pari.quadclassunit(D)[1]]
    return 0 if any(c % 4 == 0 for c in cyc) else 1


# ---------------------------------------------------------------- 2-Selmer group via local images
def sqf(q):
    """Squarefree integer representative of the square class of a nonzero rational q."""
    q = pari(q)
    return int(pari.core(pari.numerator(q) * pari.denominator(q)))


def vp(q, p):
    return int(pari.valuation(pari(q), p))


def key_p(q, p):
    q = pari(q)
    v = vp(q, p)
    u = q / pari(p) ** v
    if p == 2:
        num, den = int(pari.numerator(u)), int(pari.denominator(u))
        return (v % 2, (num * pow(den, -1, 8)) % 8)
    num, den = int(pari.numerator(u)), int(pari.denominator(u))
    return (v % 2, leg_bit(p, num * den))


def is_sq_p(q, p):
    if q == 0:
        return True
    k = key_p(q, p)
    return k[0] == 0 and (k[1] == 1 if p == 2 else k[1] == 0)


def kummer_rat(d, x):
    """Kummer map of the affine point with abscissa x (rational), as in Lean's `kummer`."""
    if x == 0:
        return (-1, -d)
    if x == d:
        return (d, 2)
    if x == -d:
        return (-d, -2 * d)
    return (x, x - d)


def local_image(d, p):
    target = 8 if p == 2 else 4
    img = set()
    for x in (0, d, -d):
        a, b = kummer_rat(d, x)
        img.add((key_p(a, p), key_p(b, p)))
    img.add(((0, 1 if p == 2 else 0), (0, 1 if p == 2 else 0)))  # point at infinity
    for k in range(-4, 6):
        for t in range(1, 8 * p ** 2 + 1):
            for s in (1, -1):
                x = pari(s * t) * pari(p) ** k
                f = x * (x - d) * (x + d)
                if f != 0 and is_sq_p(f, p):
                    a, b = kummer_rat(d, x)
                    img.add((key_p(a, p), key_p(b, p)))
            if len(img) >= target:
                break
        if len(img) >= target:
            break
    assert len(img) == target, (d, p, len(img))
    return img


def sel2(d):
    P = primes_of(d)
    bad = [2] + P
    imgs = {p: local_image(d, p) for p in bad}
    supp = [-1, 2] + P
    gens = []
    for e in itertools.product((0, 1), repeat=len(supp)):
        v = 1
        for ei, q in zip(e, supp):
            if ei:
                v *= q
        gens.append(v)
    out = []
    for a in gens:
        for b in gens:
            if not ((a > 0 and b > 0) or (a < 0 and b < 0)):  # Loc R
                continue
            if all((key_p(a, p), key_p(b, p)) in imgs[p] for p in bad):
                out.append((a, b))
    return out


# ---------------------------------------------------------------- points
def loc_Q_witness(d, a, b, x):
    """Lean Loc Q d a b, second alternative, with witness x."""
    x = pari(x)
    return (pari.issquare(x / a) and pari.issquare((x - d) / b)
            and pari.issquare((x + d) / (a * b)))


def points_cover(d, S):
    E = pari.ellinit([0, 0, 0, -d * d, 0])
    try:
        rk = pari.ellrank(E)
    except Exception as exc:  # noqa: BLE001
        return None, str(exc), {}
    lo, hi = int(rk[0]), int(rk[1])
    pts = list(rk[3])
    tors = [pari('[0,0]'), pari([d, 0]), pari([-d, 0])]
    # span of the torsion and the points found; for every class keep a point P realizing it
    reps = {(1, 1): pari('[0]')}
    for G in tors + pts:
        ka, kb = kummer_rat(d, G[0])
        kG = (sqf(ka), sqf(kb))
        new = {}
        for cls, P in reps.items():
            nk = (sqf(cls[0] * kG[0]), sqf(cls[1] * kG[1]))
            if nk not in reps and nk not in new:
                new[nk] = pari.elladd(E, P, G)
        reps.update(new)
    witnesses = {}
    if pts:
        G2 = pari.ellmul(E, pts[0], 2)
        for cls, P in reps.items():
            R = pari.elladd(E, P, G2)  # non-torsion, same class
            witnesses[cls] = bool(loc_Q_witness(d, cls[0], cls[1], R[0]))
    return (lo, hi), None, {c: witnesses.get(c, False) for c in reps}


def main(ds):
    print("d | primes | #Sel2 | T5b | genusSum5b | detM5b | #adm | g(Redei)=g(PARI) on blocks | "
          "ellrank | an.rank | classes realized")
    for d in ds:
        bits = Bits(d)
        S = sel2(d)
        t, nadm = T5b(bits)
        gs = genusSum5b(bits)
        dm = detM5b(bits)
        # Redei check on every nonempty B with class != 5 (the blocks T5b can use)
        bad_g = []
        for k in range(1, bits.r + 1):
            for B in itertools.combinations(range(bits.r), k):
                if bits.dprod(B) % 8 == 5:
                    continue
                if bits.redeiG(list(B)) != g_pari(bits.dprod(B)):
                    bad_g.append(bits.dprod(B))
        nblocks = sum(1 for k in range(1, bits.r + 1)
                      for B in itertools.combinations(range(bits.r), k) if bits.dprod(B) % 8 != 5)
        rk, err, wit = points_cover(d, S)
        try:
            ar = int(pari.ellanalyticrank(pari.ellinit([0, 0, 0, -d * d, 0]))[0])
        except Exception:  # noqa: BLE001
            ar = None
        realized = sum(1 for ab in S if wit.get((sqf(ab[0]), sqf(ab[1])), False))
        missing = [ab for ab in S if not wit.get((sqf(ab[0]), sqf(ab[1])), False)]
        print(f"{d} | {bits.P} | {len(S)} | {t} | {gs} | {dm} | {nadm} | "
              f"{'ok' if not bad_g else 'MISMATCH ' + str(bad_g)} ({nblocks} blocks) | "
              f"{rk if err is None else 'ERR ' + err} | {ar} | {realized}/{len(S)}"
              + ("" if not missing else f" missing {missing}"))
        sys.stdout.flush()


if __name__ == "__main__":
    DS = [5, 13, 29, 85, 205, 221, 365,
          21, 69, 77, 93, 133, 141, 165, 237, 253, 285, 301, 309, 357,
          413, 429, 469, 517, 589, 645, 741, 1365, 2109, 4389]
    main(DS)
