"""h29-fix: TYZ's 8-point double coset space, pi^U, the test vectors f_n and Q(n) at small n.

Model (derived in docs/research/h29-fix.md §2 from B^ x = B^x O^_B^x, TYZ L667):
  X = B^x \\ B^^x / Q^^x U  =  O_B^x \\ (O_B/4 O_B)^x       (U = O^_B^{2,x} Z_2^x (1 + 4 O_{B,2}))
a class of g in O_{B,2}^x (component 1 off 2) is the left O_B^x-orbit of g mod 4.
Right translation by u in O_{B,2}^x is right multiplication mod 4; T_p (p odd) is
  (T_p f)(x) = (1/24) sum_{alpha in O_B, nrd alpha = p} f(alpha x)        (x alpha_p ~ alpha^{-1} x at 2).
Everything is exact integer / rational arithmetic.

Quaternions in O_B are stored doubled: q = (a + b i + c j + d k)/2, a = b = c = d (mod 2).
"""
from fractions import Fraction
from itertools import product
import sys

def qmul2(p, q):
    """doubled coords of (p/2)(q/2)*2 ... input doubled coords of P, Q in O_B; output doubled coords of PQ."""
    a1, b1, c1, d1 = p
    a2, b2, c2, d2 = q
    r = (a1*a2 - b1*b2 - c1*c2 - d1*d2,
         a1*b2 + b1*a2 + c1*d2 - d1*c2,
         a1*c2 - b1*d2 + c1*a2 + d1*b2,
         a1*d2 + b1*c2 - c1*b2 + d1*a2)
    assert all(x % 2 == 0 for x in r)
    return tuple(x // 2 for x in r)

def nrd2(q):
    s = sum(x*x for x in q)
    assert s % 4 == 0
    return s // 4

def coords(q):
    """O_B = Z<1, i, j, zeta>, zeta = (-1+i+j+k)/2: integer coordinates (x0,x1,x2,x3)."""
    a, b, c, d = q
    assert (a + d) % 2 == 0 and (b - d) % 2 == 0 and (c - d) % 2 == 0
    return ((a + d)//2, (b - d)//2, (c - d)//2, d)

def from_coords(x):
    x0, x1, x2, x3 = x
    return (2*x0 - x3, 2*x1 + x3, 2*x2 + x3, x3)

def red(q, m=4):
    return tuple(t % m for t in coords(q))

# (O_B/4)^x : residues with odd reduced norm
R4 = [x for x in product(range(4), repeat=4)]
UNITS4 = [x for x in R4 if nrd2(from_coords(x)) % 2 == 1]
assert len(UNITS4) == 192, len(UNITS4)

def mul4(x, y):
    return red(qmul2(from_coords(x), from_coords(y)))

# O_B^x: the 24 Hurwitz units, doubled coordinates
OBX = [q for q in product(range(-2, 3), repeat=4)
       if all((t - q[0]) % 2 == 0 for t in q) and sum(t*t for t in q) == 4]
assert len(OBX) == 24
OBX4 = [red(q) for q in OBX]

# left O_B^x-orbits
cls = {}
reps = []
for x in UNITS4:
    if x in cls:
        continue
    orb = {mul4(u, x) for u in OBX4}
    for y in orb:
        cls[y] = len(reps)
    reps.append(x)
NX = len(reps)
assert NX == 8, NX           # TYZ Lemma 2.5: 8 classes
orbsize = {}
for y, c in cls.items():
    orbsize[c] = orbsize.get(c, 0) + 1
assert all(v == 24 for v in orbsize.values())   # free action: uniform measure (TYZ Lemma 2.5)

ONE = red((2, 0, 0, 0))
# TYZ's representatives 1 + 2x, x in {a i + b j + c zeta}
def two_rep(abc):
    a, b, c = abc
    return (1, 2*a, 2*b, 2*c)
TWOREPS = {abc: cls[two_rep(abc)] for abc in product(range(2), repeat=3)}
assert sorted(TWOREPS.values()) == list(range(8))   # 1 + 2x, x in O_B/(Z+2O_B), are the 8 classes

def nrd4(x):
    return nrd2(from_coords(x)) % 4

chi0 = [1 if nrd4(reps[c]) == 1 else -1 for c in range(NX)]   # chi_0 o nrd, nrd mod 4

# ---- linear algebra over Q -------------------------------------------------
def rref(rows, ncols):
    M = [[Fraction(v) for v in r] for r in rows]
    piv = []
    r = 0
    for c in range(ncols):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        M[r] = [v / M[r][c] for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f*b for a, b in zip(M[i], M[r])]
        piv.append(c)
        r += 1
    return M[:r], piv

def nullspace(rows, ncols):
    M, piv = rref(rows, ncols)
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for fc in free:
        v = [Fraction(0)] * ncols
        v[fc] = Fraction(1)
        for i, pc in enumerate(piv):
            v[pc] = -M[i][fc]
        basis.append(v)
    return basis

# A_0^U: functions on X orthogonal to 1 and chi_0 o nrd (uniform measure)
A0 = nullspace([[1]*NX, chi0], NX)
assert len(A0) == 6                        # TYZ Thm 2.4(1): dim pi^U = 6

# ---- Hecke operators --------------------------------------------------------
def ap_E(p):
    """a_p of E: y^2 = x^3 - x, by point count."""
    cnt = 1
    for x in range(p):
        r = (x**3 - x) % p
        cnt += 1 if r == 0 else (2 if pow(r, (p-1)//2, p) == 1 else 0)
    return p + 1 - cnt

def hurwitz_norm(p):
    B = 2 * int(p**0.5) + 2
    return [q for q in product(range(-B, B+1), repeat=4)
            if all((t - q[0]) % 2 == 0 for t in q) and sum(t*t for t in q) == 4*p]

def Tp_matrix(p):
    al = [red(q) for q in hurwitz_norm(p)]
    assert len(al) == 24 * (p + 1)
    M = [[Fraction(0)]*NX for _ in range(NX)]
    for c in range(NX):
        x = reps[c]
        for a in al:
            M[c][cls[mul4(a, x)]] += Fraction(1, 24)
    return M      # (T f)(x_c) = sum_d M[c][d] f(x_d)

def apply(M, f):
    return [sum(M[c][d]*f[d] for d in range(NX)) for c in range(NX)]

def primes(lo, hi):
    return [p for p in range(lo, hi) if all(p % q for q in range(2, int(p**0.5)+1)) and p > 1]

def hecke_check(bound=60):
    out = []
    for p in primes(3, bound):
        M = Tp_matrix(p)
        a = ap_E(p)
        ok = all(apply(M, f) == [a*v for v in f] for f in A0)
        one = apply(M, [1]*NX) == [p+1]*NX
        chi = apply(M, chi0) == [(1 if p % 4 == 1 else -1)*(p+1)*v for v in chi0]
        out.append((p, a, ok, one, chi))
    return out

# ---- the test vector f_n ----------------------------------------------------
def int_generator(basis):
    """primitive integer vector spanning a 1-dim Q-space"""
    assert len(basis) == 1
    v = basis[0]
    from math import gcd
    L = 1
    for t in v:
        L = L * t.denominator // gcd(L, t.denominator)
    w = [int(t * L) for t in v]
    g = 0
    for t in w:
        g = gcd(g, abs(t))
    return [t // g for t in w]

def test_vector(abc_tau, n):
    """TYZ's f_n for n = 3 (mod 8) [K_2 = Q_2(sqrt(-n)) unramified]: tau(sqrt(-n)) = a i + b j + c k.
    U_n = U K_{n,2}^x and K_{n,2}^x = Q_2^x O_{K,2}^x, so pi^{U_n} = right tau(O_K/4)^x-invariants of A_0^U."""
    a, b, c = abc_tau
    assert a*a + b*b + c*c == n
    # tau(omega) = (-1 + tau(sqrt(-n)))/2, omega = (-1 + sqrt(-n))/2  (n = 3 mod 4)
    om = (-1, a, b, c)
    # (O_K/4)^x generated (as a set) by u + v omega
    gens = set()
    for u, v in product(range(4), repeat=2):
        q = (2*u - v, v*a, v*b, v*c)             # doubled coords of u + v tau(omega)
        if nrd2(q) % 2 == 1:
            gens.add(red(q))
    rows = []
    for g in gens:
        # f(x g) = f(x) for every class x
        for c_ in range(NX):
            row = [Fraction(0)]*NX
            row[cls[mul4(reps[c_], g)]] += 1
            row[c_] -= 1
            rows.append(row)
    rows += [[1]*NX, chi0]
    sp = nullspace(rows, NX)
    return sp, gens

def report():
    print("classes X =", NX, "(TYZ Lemma 2.5: 8)")
    print("orbit sizes all 24 (free O_B^x/{+-1}... action of O_B^x on (O_B/4)^x)")
    print("reps 1+2x, x = a i + b j + c zeta:", TWOREPS)
    print("chi_0 o nrd on classes:", chi0)
    print("dim A_0^U =", len(A0))
    for row in hecke_check(int(sys.argv[1]) if len(sys.argv) > 1 else 60):
        print("p=%d a_p=%d  T_p = a_p on A_0^U: %s   T_p 1=(p+1)1: %s   T_p chi0=chi0(p)(p+1)chi0: %s" % row)
    # n = 3, all 8 admissible tau (tau(omega) a Hurwitz unit with real part -1/2)
    for n, taus in [(3, [s for s in product((1, -1), repeat=3)]),
                    (11, [(1, 1, 3), (3, 1, 1), (-1, 1, 3), (1, -3, 1)]),
                    (19, [(1, 3, 3), (3, 3, 1), (-3, 1, 3)])]:
        for t in taus:
            sp, gens = test_vector(t, n)
            assert len(sp) == 1, (n, t, len(sp))     # TYZ Thm 2.6: one-dimensional
            f = int_generator(sp)
            vals = sorted(set(f))
            print("n=%d tau(sqrt-n)=%s: dim pi^{U_n}=1, f_n on classes=%s, values=%s, Q(n)=f_n(1)=%d"
                  % (n, t, f, vals, f[cls[ONE]]))

if __name__ == "__main__":
    report()
