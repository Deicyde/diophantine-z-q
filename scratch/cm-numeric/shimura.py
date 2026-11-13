"""Numerical check of cm-points' leaf CM.ShimuraReciprocity (ZInQKernel/Contrib/TYZGenus/CM.lean):
for an odd split prime p, b^2 = D (mod 4p), and sigma an arithmetic Frobenius at a prime P of Qbar
containing p and (-b + sqrt D)/2 (sqrt D = i sqrt|D| under iota_C), sigma maps the Heegner point of
Q to that of Q' whenever (<1,tau'>, <1/32,tau'>) = c * pbar * (<1,tau>, <1/32,tau>),
pbar = <p, (-b - sqrt D)/2>, and B' = B (mod 64).

Method.  Q' is computed from the lattice condition (exact arithmetic in K = Q(sqrt D)).  For the h
Heegner points x_r (one per class, B = beta mod 64) put F = prod (X - x_r) in K[X] and let g in K[X]
interpolate x_r -> x(Q'_r).  The arithmetic Frobenius at P satisfies sigma(x) = x^p mod P, so the
statement holds for all r iff  g(X) = X^p  in (O_K/P)[X]/(F mod P) = F_p[X]/(F mod (p, sqrt D - b)).
The same test is run for the opposite direction (p instead of pbar), which must fail when the class
of p has order > 2."""
from fractions import Fraction as Fr
from math import gcd
import sys
from heeg import *

# ---- exact arithmetic in K = Q(sqrt D): elements (u, v) = u + v sqrt D ----
def kmul(a, b, D):
    return (a[0]*b[0] + D*a[1]*b[1], a[0]*b[1] + a[1]*b[0])

def lattice_hnf(gens):
    """Z-span of elements of K (u, v rationals) -> basis of 2 elements (HNF on scaled coords)."""
    den = 1
    for (u, v) in gens:
        den = den*Fr(u).denominator//gcd(den, Fr(u).denominator)
        den = den*Fr(v).denominator//gcd(den, Fr(v).denominator)
    rows = [[int(Fr(u)*den), int(Fr(v)*den)] for (u, v) in gens]
    M = pari.matrix(len(rows), 2, [t for r in rows for t in r])
    H = pari.mathnf(pari.mattranspose(M))      # columns form a basis
    basis = []
    for j in range(int(pari.matsize(H)[1])):
        basis.append((Fr(int(H[0, j]), den), Fr(int(H[1, j]), den)))
    assert len(basis) == 2
    return basis

def lat_mul(L1, L2, D):
    return lattice_hnf([kmul(a, b, D) for a in L1 for b in L2])

def coords(basis, w):
    """Coordinates of w in a Q-basis (2 elements) of K."""
    (a, b), (c, d) = basis
    det = a*d - b*c
    x = (w[0]*d - w[1]*c)/det
    y = (a*w[1] - b*w[0])/det
    return x, y

def form_from_tau(t, D):
    """t = s + r sqrt D with r > 0 (Im > 0): the primitive form [A,B,C] with root t."""
    s, r = t
    A = Fr(1, 2)/r
    B = -s/r
    assert A.denominator == 1 and B.denominator == 1, (s, r)
    A, B = int(A), int(B)
    C = Fr(B*B - D, 4*A)
    assert C.denominator == 1
    return (A, B, int(C))

def pair_image(Q, Ilat, D, N=32):
    """Q' with (<1,tau'>, <1/N,tau'>) = c * I * (<1,tau>, <1/N,tau>)."""
    A, B, C = Q
    tau = (Fr(-B, 2*A), Fr(1, 2*A))
    L = lat_mul(Ilat, [(Fr(1), Fr(0)), tau], D)
    LN = lat_mul(Ilat, [(Fr(1, N), Fr(0)), tau], D)
    # coordinates of L in LN
    cols = [coords(LN, w) for w in L]
    for x, y in cols:
        assert x.denominator == 1 and y.denominator == 1
    # find v in L, primitive in LN, with L = Z v + N LN
    e1, e2 = LN
    best = None
    for i in range(-N, N+1):
        for j in range(-N, N+1):
            x = i*cols[0][0] + j*cols[1][0]
            y = i*cols[0][1] + j*cols[1][1]
            if gcd(int(x), int(y)) == 1:
                best = (int(x), int(y)); break
        if best: break
    x, y = best
    # complete (x, y) to a unimodular basis: u = (x', y') with x*y' - y*x' = 1
    g, s1, t1 = pari.gcdext(x, y)[2], pari.gcdext(x, y)[0], pari.gcdext(x, y)[1]
    # x*s1 + y*t1 = 1  ->  u = (-t1, s1)
    ux, uy = -int(t1), int(s1)
    v = (x*e1[0] + y*e2[0], x*e1[1] + y*e2[1])
    u = (ux*e1[0] + uy*e2[0], ux*e1[1] + uy*e2[1])
    # check L = Z v + Z N u
    Lc = lattice_hnf([v, (N*u[0], N*u[1])])
    assert sorted(Lc) == sorted(L) or lattice_hnf(L + Lc) == Lc and lattice_hnf(Lc + L) == L
    # tau' = v / (N u)
    Nu = (N*u[0], N*u[1])
    nrm = Nu[0]**2 - D*Nu[1]**2
    tp = kmul(v, (Nu[0]/nrm, -Nu[1]/nrm), D)
    if tp[1] < 0:
        tp = (-tp[0], -tp[1])          # v -> -v keeps both lattices
    return form_from_tau(tp, D)

def recog_K(c, D, bound=10**60):
    u = pari.real(c)
    v = pari.imag(c)/pari(f"sqrt({-D})")
    ur, vr = pari.bestappr(u, bound), pari.bestappr(v, bound)
    err = abs(c - (ur + vr*pari(f"I*sqrt({-D})")))
    return Fr(int(pari.numerator(ur)), int(pari.denominator(ur))), Fr(int(pari.numerator(vr)), int(pari.denominator(vr))), err

out = []
def say(*a):
    s = ' '.join(str(t) for t in a); print(s, flush=True); out.append(s)

def run(D, beta, primes):
    reps = heegner_reps(D, beta)
    h = int(pari.qfbclassno(D)) if D % 4 in (0, 1) else None
    forms = list(reps.values())
    say(f'D={D} beta={beta} h={len(forms)} (qfbclassno {h}); reps: {forms}')
    xs = [xy(tau_of(a, b, D))[0] for (a, b, c) in forms]
    X = pari('X')
    F = pari(1)
    for x in xs: F *= (X - x)
    Fc = [recog_K(F.polcoef(k), D) for k in range(len(forms)+1)]
    say(f'  F in K[X]: max recognition error {float(max(e for _,_,e in Fc)):.1e}; denominators {sorted(set(u.denominator for u,_,_ in Fc) | set(v.denominator for _,v,_ in Fc))}')
    nchecked = 0
    for p in primes:
        if D % p == 0 or pari.kronecker(D, p) != 1: continue
        b = next(bb for bb in range(2*p) if (bb*bb - D) % (4*p) == 0)
        res = {}
        for name, sgn in (('pbar', -1), ('p', +1)):
            Ilat = [(Fr(p), Fr(0)), (Fr(-b, 2), Fr(sgn, 2))]
            imgs = [pair_image(Q, Ilat, D) for Q in forms]
            bok = all((Qp[1] - Q[1]) % 64 == 0 for Q, Qp in zip(forms, imgs))
            ys = [xy(tau_of(a, bb, D))[0] for (a, bb, c) in imgs]
            g = pari.polinterpolate(xs, ys)
            gc = [recog_K(g.polcoef(k), D) for k in range(len(forms))]
            gerr = max(e for _, _, e in gc) if gc else 0
            # reduce mod P: sqrt D -> b
            def red(uv):
                u, v = uv[0], uv[1]
                val = (u + v*b)
                return pari.Mod(val.numerator, p)/pari.Mod(val.denominator, p)
            Fp = pari.Pol([red(c[:2]) for c in reversed(Fc)], 'X')
            gp_ = pari.Pol([red(c[:2]) for c in reversed(gc)], 'X') if gc else pari(0)
            Xp = pari.Mod(pari('X'), Fp)**p
            ok = (pari.Mod(gp_, Fp) == Xp)
            sqf = pari.poldegree(pari.gcd(Fp, pari.deriv(Fp))) == 0
            res[name] = (ok, bok, float(gerr), sqf)
        # order of the class of p in Cl(D)
        pf = pari.qfbprimeform(D, p)
        o = 1; q = pf
        while pari.qfbred(q) != pari.qfbred(pari.qfbpow(pf, 0)) if False else (pari.Vec(pari.qfbred(q))[:3] != pari.Vec(pari.qfbred(pari.qfbpow(pf, 0)))[:3]):
            q = pari.qfbcomp(q, pf); o += 1
        say(f'  p={p} b={b} ord[p]={o}: Frob = mult by pbar: {res["pbar"][0]} (B mod 64 kept {res["pbar"][1]}, g in K[X] err {res["pbar"][2]:.0e}, F mod P squarefree {res["pbar"][3]}) | mult by p: {res["p"][0]}')
        nchecked += 1
    return nchecked

if __name__ == '__main__':
    cases = [(-23, 19), (-47, 9), (-71, 21), (-31, 15), (-39, 27), (-64*5, -8), (-64*13, -8)]
    primes = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
    total = 0
    for D, beta in cases:
        total += run(D, beta, primes[:12] if total < 25 else [])
    say(f'total (D, p) pairs checked: {total}')
    open('shimura.out', 'w').write('\n'.join(out) + '\n')
