"""E3: q-uniform route with N = beta (rs-pole 2.2(3)/torsion first point) needs C_{beta*theta(q)}
to have a point over Q(q) with abscissa class beta, i.e. a nonconstant odd map Y -> C_1 from
Y: w^2 = beta*m*(m T(R)^2 - R N_W(R)^2), R = R0 (1 - R0 q^2)^2  (theta = m(m - R/Theta^2) mod squares,
Theta = T/N_W).  Such a map forces Jac(Y) to have a factor Qbar-isogenous to C_1: y^2 = x^3 - x,
hence for every good p = 3 mod 4 a supersingular Frobenius root (alpha^2/p a root of unity).
We compute charpoly mod p (PARI hyperellcharpoly) and look for cyclotomic factors of the
polynomial with roots alpha^2/p.  Twisting by the constant beta does not change Jac over Qbar, so
beta is omitted."""
import sys
from fractions import Fraction as Fr
import k0, cypari2
pari = cypari2.Pari(); pari.allocatemem(4*10**9)
sys.set_int_max_str_digits(0)

def polys(n, kap, h, s0, eta):
    t = Fr(n); C = [c for c in k0.testC(n, kap, t, h, s0)]
    # W(R) = prod (1 + R c^2) as polynomial in R with K0 coefficients: list of K
    W = [k0.K(1)]
    for c in C:
        c2 = c*c
        if c2.iszero(): continue
        new = [k0.K(0)]*(len(W)+1)
        for i, a in enumerate(W):
            new[i] = new[i] + a
            new[i+1] = new[i+1] + a*c2
        W = new
    T = [2*a.a for a in W]                     # W + conj W
    Wb = [a.conj() for a in W]
    NW = [Fr(0)]*(2*len(W)-1)
    for i, a in enumerate(W):
        for j, b in enumerate(Wb):
            NW[i+j] += (a*b).a
    return T, NW, k0.testR0(eta, t)

def curve_poly(n, kap, h, s0, eta, m):
    T, NW, R0 = polys(n, kap, h, s0, eta)
    x = pari('x')
    Tp = sum(pari(str(c))*pari('R')**i for i, c in enumerate(T))
    Np = sum(pari(str(c))*pari('R')**i for i, c in enumerate(NW))
    g = m*(m*Tp**2 - pari('R')*Np**2)
    Rq = pari(str(R0))*(1 - pari(str(R0))*x**2)**2
    f = pari.subst(g, 'R', Rq)
    f = f*pari.denominator(pari.content(f))
    f = f/pari.content(f)
    return f

def test(f, p):
    fp = f*pari.Mod(1, p)
    if pari.poldegree(pari.gcd(fp, pari.deriv(fp))) > 0: return ('singular mod', p)
    P = pari.hyperellcharpoly(fp)
    Q = pari.polresultant(P, pari(f'{p}*y - x^2'), 'x')      # roots alpha^2/p (polynomial in y)
    cyc = pari.polcyclofactors(Q)
    return dict(p=p, genus=int(pari.poldegree(P))//2, cyclo_factors=str(cyc))

if __name__ == "__main__":
    for (n, h, s0, eta, m) in [(1, 2, 2, 1, 1), (2, 2, 4, 1, 1)]:
        f = curve_poly(n, 1, h, s0, eta, m)
        print((n, h, s0, eta, m), 'deg', pari.poldegree(f), flush=True)
        for p in (19, 23):
            print('  ', test(f, p), flush=True)
