"""Differential check: RedeiFormula's gBit d B (transcribed from Rank5b/Sec3/Defs.lean, Matrices.lean,
Slots/Symbols.lean) against PARI's class group of Q(sqrt(-d_B)).

gBit d B = redeiG (aBit d) (yBit d) (zBit d) B with
  aBit d i j = legBit i j        ([p_j / p_i], 0 iff p_j is a square mod p_i)
  yBit d i   = legBit i (-1)     (lambda_p)
  zBit d i   = legBit i 2        (mu_p)
  lapl a U i j = sum_{k in U, k != i} a i k  if i = j  else a i j
  kappa a B rho = det (lapl a B) restricted to (B minus rho) x (B minus rho)
  redeiG = if sum_B y = 1 then sum_B y_rho kappa_rho else sum_B z_rho kappa_rho
gCl n = #(Cl^2) of Q(sqrt(-n)); RedeiFormula: gCl (d_B) mod 2 = gBit d B.
At most 30 inputs (task rule), run one after another.
"""
import itertools
import cypari2

pari = cypari2.Pari()


def is_sq_mod(a, p):
    a %= p
    return any((x * x - a) % p == 0 for x in range(p))


def legbit(p, a):
    return 0 if is_sq_mod(a, p) else 1


def det2(M):
    """Determinant over F_2 (Gaussian elimination); det of the 0x0 matrix is 1."""
    M = [row[:] for row in M]
    n = len(M)
    for c in range(n):
        piv = next((r for r in range(c, n) if M[r][c] % 2), None)
        if piv is None:
            return 0
        M[c], M[piv] = M[piv], M[c]
        for r in range(c + 1, n):
            if M[r][c] % 2:
                M[r] = [(x + y) % 2 for x, y in zip(M[r], M[c])]
    return 1


def gbit(B):
    a = {(i, j): legbit(i, j) for i in B for j in B if i != j}
    y = {i: legbit(i, -1) for i in B}
    z = {i: legbit(i, 2) for i in B}

    def lapl(i, j):
        if i == j:
            return sum(a[(i, k)] for k in B if k != i) % 2
        return a[(i, j)]

    def kappa(rho):
        idx = [i for i in B if i != rho]
        return det2([[lapl(i, j) for j in idx] for i in idx])

    if sum(y.values()) % 2 == 1:
        return sum(y[r] * kappa(r) for r in B) % 2
    return sum(z[r] * kappa(r) for r in B) % 2


def gcl_parity(n):
    D = -n if n % 4 == 3 else -4 * n
    cyc = [int(c) for c in pari(f"quadclassunit({D})[2]")]
    sq = 1
    for c in cyc:
        sq *= c // (2 if c % 2 == 0 else 1)
    return sq % 2, cyc


def primes_of(d):
    return [int(p) for p in pari(f"factor({d})[,1]~")]


# (d, B) pairs: d odd squarefree, B a nonempty subset of its primes, d_B = 7, 3 or 1 mod 8.
# Chosen to cover 1-4 primes in B, each class mod 8, and both parities of #2Cl.
PAIRS = [
    (7 * 5, [7]), (23 * 3, [23]), (7 * 113 * 5, [7, 113]), (31 * 17, [31, 17]),
    (7 * 41 * 73, [7, 41, 73]), (3 * 5 * 13 * 17, [3, 5]), (127 * 17 * 3, [127, 17]),
    (7 * 17 * 41 * 3, [7, 17, 41]), (11 * 13, [11, 13]), (3 * 17 * 5, [3, 17]),
    (19 * 41, [19, 41]), (43 * 113 * 7, [43, 113]), (3 * 73 * 89, [3, 73, 89]),
    (11 * 17 * 73 * 97, [11, 17, 73, 97]), (3 * 5 * 7 * 11 * 13, [3, 5, 7, 11, 13]),
    (17 * 5, [17]), (41 * 3, [41]), (3 * 11 * 7, [3, 11]), (17 * 73, [17, 73]),
    (5 * 13 * 7, [5, 13]), (17 * 41 * 113, [17, 41, 113]), (3 * 19 * 23 * 5, [3, 19]),
    (7 * 23 * 5, [7, 23]), (41 * 73 * 89 * 97, [41, 73, 89, 97]), (113 * 3, [113]),
    (5 * 29 * 37, [5, 29]), (7 * 31 * 3, [7, 31, 3]), (3 * 5 * 7, [3, 5, 7]),
    (19 * 5, [19]), (5 * 37 * 13 * 3, [5, 13, 3]),
]
assert len(PAIRS) <= 30

bad = 0
for d, B in PAIRS:
    assert d % 2 == 1 and int(pari(f"issquarefree({d})"))
    assert set(B) <= set(primes_of(d))
    dB = 1
    for p in B:
        dB *= p
    assert dB % 8 in (1, 3, 7), (d, B, dB % 8)
    par, cyc = gcl_parity(dB)
    g = gbit(B)
    ok = par == g
    bad += not ok
    print(f"d={d:>9} B={B!s:<22} d_B={dB:>9} mod8={dB % 8} Cl={cyc!s:<14} #2Cl mod 2={par} gBit={g} {'ok' if ok else 'MISMATCH'}")
print("pairs:", len(PAIRS), "mismatches:", bad)
