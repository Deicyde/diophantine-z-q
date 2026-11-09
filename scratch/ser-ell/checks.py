"""Independent checks for the audit of route 1 (Serre's argument at large l).

A. The order O = Z[i,(1+j)/2] in B = (2,-3) has reduced discriminant 6, so O/lO = M_2(F_l)
   for every prime l not dividing 6 (step 1 needs this).
B. Serre's weight recipe (Serre 1987, section 2, as restated in the proof of
   Buzzard-Diamond-Jarvis, Theorem 3.15 of arXiv 0810.2106v5) evaluated on every inertia type
   that Raynaud's theorem allows for a finite flat F-vector space scheme of rank 2 over an
   unramified base (e = 1): tame characters are products of fundamental characters with
   exponents in {0, 1}.  With det = omega on inertia the weight is always 2 (step 3).
C. The determinant: det rbar|I_l = omega * eta with eta quadratic must lie in
   {1, omega, omega^2} (Raynaud).  This forces eta = 1 exactly when l > 3.
Run with any Python 3; no dependencies.
"""
from fractions import Fraction as Fr
from itertools import product


def primes(lo, hi):
    return [p for p in range(lo, hi) if p > 1 and all(p % q for q in range(2, int(p**0.5) + 1))]


# ---------- A. quaternion order ----------
A_, B_ = 2, -3  # i^2 = 2, j^2 = -3, ij = -ji


def qmul(x, y):
    """Multiply quaternions in basis (1, i, j, ij) of (A_, B_)."""
    a1, b1, c1, d1 = x
    a2, b2, c2, d2 = y
    return (
        a1 * a2 + A_ * b1 * b2 + B_ * c1 * c2 - A_ * B_ * d1 * d2,
        a1 * b2 + b1 * a2 - B_ * c1 * d2 + B_ * d1 * c2,
        a1 * c2 + c1 * a2 + A_ * b1 * d2 - A_ * d1 * b2,
        a1 * d2 + d1 * a2 + b1 * c2 - c1 * b2,
    )


def trd(x):
    return 2 * x[0]


h = Fr(1, 2)
basis = [(1, 0, 0, 0), (0, 1, 0, 0), (h, 0, h, 0), (0, h, 0, h)]  # 1, i, (1+j)/2, (i+ij)/2


def coords(x):
    """Coordinates of x in the O-basis (solve the triangular system)."""
    a, b, c, d = x
    z2 = 2 * c          # coefficient of (1+j)/2
    z3 = 2 * d          # coefficient of (i+ij)/2
    z0 = a - z2 * h
    z1 = b - z3 * h
    return (z0, z1, z2, z3)


def det(m):
    m = [row[:] for row in m]
    n, s = len(m), Fr(1)
    for c in range(n):
        piv = next((r for r in range(c, n) if m[r][c] != 0), None)
        if piv is None:
            return Fr(0)
        if piv != c:
            m[c], m[piv] = m[piv], m[c]
            s = -s
        s *= m[c][c]
        for r in range(c + 1, n):
            f = Fr(m[r][c]) / m[c][c]
            m[r] = [m[r][k] - f * m[c][k] for k in range(n)]
    return s


closed = all(all(Fr(z).denominator == 1 for z in coords(qmul(x, y))) for x in basis for y in basis)
gram = [[Fr(trd(qmul(x, y))) for y in basis] for x in basis]
disc = det(gram)
print("A. O closed under multiplication:", closed)
print("A. det(Trd(e_a e_b)) =", disc, "(maximal order of reduced discriminant 6 <=> |det| = 36)")
print("A. hence O/lO is central simple, = M_2(F_l) by Wedderburn, for all l not dividing 6")

# ---------- B. Serre's recipe on finite flat types ----------


def serre_k_semisimple_level1(l, al, be):
    """rho|I = omega^al + omega^be, exponents in [0, l-2]; Serre's recipe."""
    a, b = sorted((al % (l - 1), be % (l - 1)))
    if (a, b) == (0, 0):
        return l
    return 1 + l * a + b


def serre_k_nonsplit(l, be, al, peu):
    """rho|I = (omega^be *; 0 omega^al) non-semisimple, Serre's recipe (2.3)-(2.4)."""
    al %= l - 1
    be %= l - 1
    if be == 0:
        be = l - 1
    if be == (al + 1) % (l - 1) or (al == l - 2 and be == l - 1):
        # beta = alpha + 1: the peu/tres ramifie dichotomy
        if al == l - 2 and be == l - 1:
            pass
        return 1 + l * al + be + (0 if peu else l - 1)
    a, b = min(al, be), max(al, be)
    return 1 + l * a + b


def serre_k_level2(l, m):
    """rho|I = psi^m + psi^{lm}, psi fundamental of level 2, m not divisible by l+1."""
    # write m = a + l*b ... with 0 <= a < b <= l-1 after possibly swapping to psi^{lm}
    for mm in (m % (l * l - 1), (l * m) % (l * l - 1)):
        a, b = mm % l, mm // l
        if 0 <= a < b <= l - 1:
            return 1 + l * a + b
    raise ValueError


bad = []
for l in primes(5, 120):
    ks = {}
    # level 2: Raynaud exponents (e0, e1) in {0,1}^2 give psi^{e0 + l e1}; irreducible needs
    # e0 != e1, i.e. psi^1 + psi^l (or its swap): m = l (a=0, b=1).
    for e0, e1 in product((0, 1), repeat=2):
        m = e0 + l * e1
        if m % (l + 1) == 0:
            continue  # level-1 character, not an irreducible level-2 type
        ks[("level2", e0, e1)] = serre_k_level2(l, m)
    # level 1 semisimple with exponents in {0,1}
    for al, be in product((0, 1), repeat=2):
        ks[("ss", al, be)] = serre_k_semisimple_level1(l, al, be)
    # level 1 non-semisimple from connected-etale: sub = connected (omega), quotient = etale (1);
    # finite flat extensions are peu ramifiees
    ks[("nonsplit-peu", 1, 0)] = serre_k_nonsplit(l, 1, 0, peu=True)
    ks[("nonsplit-tres", 1, 0)] = serre_k_nonsplit(l, 1, 0, peu=False)  # not finite flat
    # impose det|I = omega (exponent 1 mod l-1)
    for key, k in ks.items():
        kind = key[0]
        if kind == "level2":
            dexp = (key[1] + l * key[2]) * (1 + l) % (l * l - 1)  # det = psi^{m(1+l)}
            dexp = dexp // (l + 1)  # as a power of omega = psi^{l+1}
        elif kind == "ss":
            dexp = key[1] + key[2]
        else:
            dexp = key[1] + key[2]
        ok_det = dexp % (l - 1) == 1
        fflat = kind != "nonsplit-tres"
        if ok_det and fflat and k != 2:
            bad.append((l, key, k))
    if l in (5, 7, 113):
        print("B. l =", l, {k: v for k, v in ks.items()})
print("B. finite flat types with det = omega and weight != 2:", bad if bad else "none",
      "(l = primes in [5,120))")

# ---------- C. determinant ----------
for l in primes(3, 60):
    allowed = {0, 1, 2 % (l - 1)}
    etas = {0, (l - 1) // 2}
    forced = sorted({e for e in etas if (1 + e) % (l - 1) in allowed})
    if l <= 7 or forced != [0]:
        print("C. l =", l, "quadratic eta|I allowed:", forced)
print("C. eta|I forced trivial for every prime 5 <= l < 60")
