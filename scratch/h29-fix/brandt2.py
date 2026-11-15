"""h29-fix: TYZ's test vectors and genus periods Q(n) with class groups, n = 1 and 3 (mod 8).

Extends brandt.py (same model X = O_B^x \\ (O_B/4)^x):
* right action of K_{n,2}^x: O_{K,2}^x by right multiplication mod 4; for n = 1 (mod 8) also the uniformizer
  varpi = 1 + tau(sqrt -n) (norm 1 + n = 2 mod 8), acting by x -> lambda^{-1} x varpi = (conj(lambda) x varpi)/2
  mod 4, lambda = 1 + i (left multiplication by the global lambda^{-1} returns the 2-component to O_{B,2}^x);
* an ideal a of O_K of odd norm N, read as a finite idele and mapped by tau-hat, lies in the class of
  gamma^{-1} ~ conj(gamma), where gamma in tau(a) O_B has nrd gamma = N (O_B has class number one, TYZ L667);
* 2Cl_n from PARI (bnfinit / bnfisprincipal), Q(n) = sum_{t in 2Cl_n} f_n(t).
Checks: Lemma 2.9 with w_K (Q(n) = w_K * sum eps L(d1) L(d2) for some signs) against PARI's L-values, and
Proposition 2.3 (f_n odd on 2Cl_n).
"""
import sys
from itertools import product
from math import gcd, isqrt
from fractions import Fraction
sys.path.insert(0, __import__('os').path.dirname(__file__))
from brandt import (qmul2, nrd2, coords, from_coords, red, mul4, cls, reps, NX, chi0, nullspace,
                    int_generator, ONE)
import cypari2
pari = cypari2.Pari()
pari.set_real_precision(40)

def conj2(q):
    a, b, c, d = q
    return (a, -b, -c, -d)

def is_hurwitz2(q):
    return all((t - q[0]) % 2 == 0 for t in q)

LAM = (2, 2, 0, 0)          # lambda = 1 + i, doubled

def tau_choices(n):
    """tau(sqrt -n) = a i + b j + c k, n = a^2 + b^2 + c^2; for n = 1 (8): 4 | c; for n = 3 (8): a, b, c odd."""
    out = []
    B = isqrt(n)
    for a in range(-B, B + 1):
        for b in range(-B, B + 1):
            c2 = n - a*a - b*b
            if c2 < 0:
                continue
            c = isqrt(c2)
            if c*c != c2:
                continue
            for cc in {c, -c}:
                if n % 8 == 1 and cc % 4 == 0:
                    out.append((a, b, cc))
                if n % 8 == 3 and a % 2 and b % 2 and cc % 2:
                    out.append((a, b, cc))
    return out

def tau2(n, abc, u, v):
    """doubled coords of tau(u + v w), w = sqrt(-n) (n = 1 mod 8) or w = (-1 + sqrt -n)/2 (n = 3 mod 8);
    u, v integers."""
    a, b, c = abc
    if n % 8 == 1:
        return (2*u, 2*v*a, 2*v*b, 2*v*c)
    return (2*u - v, v*a, v*b, v*c)

def right_action_maps(n, abc):
    """list of permutations of X induced by generators of K_{n,2}^x (mod Q_2^x and U)."""
    perms = []
    for u, v in product(range(4), repeat=2):
        q = tau2(n, abc, u, v)
        if nrd2(q) % 2 == 1:
            g = red(q)
            perms.append([cls[mul4(reps[c], g)] for c in range(NX)])
    if n % 8 == 1:
        a, b, c = abc
        varpi = (2, 2*a, 2*b, 2*c)
        assert nrd2(varpi) == 1 + n
        perm = []
        for cidx in range(NX):
            x = from_coords(reps[cidx])
            y = qmul2(qmul2(conj2(LAM), x), varpi)
            assert all(t % 2 == 0 for t in y)
            y = tuple(t // 2 for t in y)
            assert is_hurwitz2(y) and nrd2(y) % 2 == 1
            perm.append(cls[red(y)])
        perms.append(perm)
    return perms

def test_vector(n, abc):
    rows = []
    for perm in right_action_maps(n, abc):
        for c in range(NX):
            row = [Fraction(0)] * NX
            row[perm[c]] += 1
            row[c] -= 1
            rows.append(row)
    rows += [[1]*NX, chi0]
    sp = nullspace(rows, NX)
    return sp

# ---- lattices in O_B (coordinates in the basis 1, i, j, zeta) --------------------------------------
def hnf_rows(vecs):
    """row-style HNF of an integer lattice in Z^4 (full rank), upper triangular basis"""
    M = [list(v) for v in vecs]
    basis = []
    col = 0
    rows = M
    for col in range(4):
        # gcd-combine all rows on column col
        while True:
            nz = [r for r in rows if r[col] != 0]
            if len(nz) <= 1:
                break
            nz.sort(key=lambda r: abs(r[col]))
            p = nz[0]
            new = [p]
            for r in rows:
                if r is p:
                    continue
                if r[col] != 0:
                    k = r[col] // p[col]
                    r = [x - k*y for x, y in zip(r, p)]
                new.append(r)
            rows = new
        piv = [r for r in rows if r[col] != 0]
        assert len(piv) == 1, "not full rank"
        p = piv[0]
        if p[col] < 0:
            p = [-x for x in p]
        basis.append(p)
        rows = [r for r in rows if r[col] == 0 and r is not piv[0]]
        rows = [r for r in rows if any(r)]
    return basis

def in_lattice(basis, v):
    v = list(v)
    for i, b in enumerate(basis):
        if v[i] % b[i]:
            return False
        k = v[i] // b[i]
        v = [x - k*y for x, y in zip(v, b)]
    return not any(v)

OB_BASIS2 = [from_coords(e) for e in [(1,0,0,0), (0,1,0,0), (0,0,1,0), (0,0,0,1)]]

def right_ideal(gens2):
    """Z-basis (coords) of sum_g g O_B"""
    vecs = []
    for g in gens2:
        for e in OB_BASIS2:
            vecs.append(coords(qmul2(g, e)))
    return hnf_rows(vecs)

def ideal_class_in_X(n, abc, N, r):
    """O_K-ideal a = (N, sqrt(-n) - r), r^2 = -n mod N, N odd: class in X of tau-hat(idele of a)."""
    a, b, c = abc
    s = (2*(-r), 2*a, 2*b, 2*c)          # doubled tau(sqrt -n - r)
    I = right_ideal([(2*N, 0, 0, 0), s])
    B = 2 * isqrt(N) + 2
    for q0, q1, q2 in product(range(-B, B+1), repeat=3):
        r2 = 4*N - q0*q0 - q1*q1 - q2*q2
        if r2 < 0:
            continue
        q3 = isqrt(r2)
        if q3 * q3 != r2:
            continue
        for q in {(q0, q1, q2, q3), (q0, q1, q2, -q3)}:
            if is_hurwitz2(q) and in_lattice(I, coords(q)):
                return cls[red(conj2(q))]
    raise RuntimeError("no generator")

def sqrt_mod(a, N):
    return [r for r in range(N) if (r*r - a) % N == 0]

def classes_2Cl(n):
    """for K = Q(sqrt -n): list of (N, r) ideals (N, sqrt -n - r) whose classes are exactly 2Cl_n
    (one per class), using PARI."""
    bnf = pari.bnfinit(pari('y^2+%d' % n), 1)
    cyc = [int(x) for x in bnf.bnf_get_cyc()]
    h = 1
    for x in cyc:
        h *= x
    def clvec(N, r):
        I = pari.idealhnf(bnf, N, pari('y - %d' % r))   # (N, y - r), y = sqrt(-n)
        v = pari.bnfisprincipal(bnf, I, 0)
        return tuple(int(x) % m for x, m in zip(v, cyc))
    def is_square_class(v):
        return all(x % 2 == 0 for x, m in zip(v, cyc) if m % 2 == 0)
    target = h // (2 ** sum(1 for m in cyc if m % 2 == 0))
    found = {}
    found[tuple(0 for _ in cyc)] = (1, 0)
    p = 3
    while len(found) < target:
        if all(p % q for q in range(2, isqrt(p) + 1)) and n % p and pow(-n % p, (p-1)//2, p) == 1:
            for k in (1, 2):
                N = p ** k
                for r in sqrt_mod(-n % N, N):
                    v = clvec(N, r)
                    if is_square_class(v) and v not in found:
                        found[v] = (N, r)
        p += 2
    return list(found.values()), h, cyc

def lcal_sq(m):
    if m == 1:
        return 1
    I = pari('intnum(x=[1,-1/2],[oo,-3/2], 1/sqrt(x^3-x))')
    E = pari.ellinit([0, 0, 0, -m*m, 0])
    L1 = pari.lfun(E, 1)
    k = len([p for p in pari.factor(m)[0] if p != 2])
    val = L1 / (pari(2) ** (2*k - 3) * (2 / pari.sqrt(m) * I))
    x = float(val)
    rx = round(x)
    assert abs(x - rx) < 1e-8, (m, x)
    return rx

def pair_idx(m):
    return [d for d in range(1, m+1) if m % d == 0 and d % 8 == 1 and (m % 8 != 1 or d*d < m)]

def lemma29_values(m):
    """all values of w_K * sum eps L(m/d) L(d) over sign choices"""
    w = 3 if m == 3 else 1
    terms = []
    for d in pair_idx(m):
        a2, b2 = lcal_sq(m // d), lcal_sq(d)
        la, lb = isqrt(a2), isqrt(b2)
        assert la*la == a2 and lb*lb == b2
        terms.append(la * lb)
    vals = {0}
    for t in terms:
        vals = {v + s*t for v in vals for s in (1, -1)}
    return sorted({w*v for v in vals}), terms

def run(ns, ntau=2):
    for n in ns:
        taus = tau_choices(n)[:ntau]
        ideals, h, cyc = classes_2Cl(n)
        vals29, terms = lemma29_values(n)
        for abc in taus:
            sp = test_vector(n, abc)
            assert len(sp) == 1, (n, abc, len(sp))
            f = int_generator(sp)
            xs = [ideal_class_in_X(n, abc, N, r) if N > 1 else cls[ONE] for N, r in ideals]
            Q = sum(f[x] for x in xs)
            odd = all(f[x] % 2 for x in xs)
            print("n=%d tau=%s h=%d cyc=%s #2Cl=%d: f_n=%s Q(n)=%d; f_n odd on 2Cl: %s; "
                  "w_K*sum eps L L ranges over %s (terms %s): Lemma 2.9 (w_K form) %s"
                  % (n, abc, h, cyc, len(ideals), f, Q, odd, vals29, terms,
                     "OK" if Q in vals29 else "FAILS"))

if __name__ == "__main__":
    ns = [int(x) for x in sys.argv[1:]] or [3, 11, 17, 33, 41, 51, 57, 73, 89, 97, 105, 113, 123]
    run(ns)
