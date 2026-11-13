"""Class-7 base CM point of TYZ (Period7.tex L1196, L1203-1205): z_n = Heegner point of
[(n+delta^2)/4, delta, 1] on X0(32) = A, delta^2 = -n (mod 128).  Checks:
 (a) the point lies on A (eta model of x0-32);
 (b) independence of delta within delta mod 64 (delta and delta+64 give the same point),
     and delta -> -delta gives the complex conjugate point;
 (c) x(z_n) is algebraic of degree <= 2h(-n) over Q, and its conjugates are the Heegner points
     of the other classes (same B mod 64): min poly over Q = prod over classes and conj.
 (d) Z(n) = sum_{t in 2Cl_n} z_n^t: computed as the sum over the classes in the principal genus
     (Shimura reciprocity), checked to be defined over the genus field L_n (degree test)."""
import sys
from heeg import *

def deltas(n):
    return [d for d in range(128) if (d*d + n) % 128 == 0]

def add(P, Q):
    """Group law on y^2 = x^3 + 4x (affine points, no zero handling needed generically)."""
    (x1, y1), (x2, y2) = P, Q
    if abs(x1 - x2) < pari('1e-300') :
        if abs(y1 + y2) < pari('1e-300'):
            return None
        l = (3*x1**2 + 4)/(2*y1)
    else:
        l = (y2 - y1)/(x2 - x1)
    x3 = l**2 - x1 - x2
    return (x3, l*(x1 - x3) - y1)

def main():
  pass
out = []
def say(*a):
    s = ' '.join(str(t) for t in a); print(s); out.append(s)

if __name__ == '__main__':
    for n in [7, 15, 23, 31, 39, 47, 55, 71]:
        D = -n
        h = int(pari.qfbclassno(D))
        ds = deltas(n)
        say(f'n={n} h(-n)={h} deltas mod 128: {ds}')
        d0 = ds[0]
        A = (n + d0*d0)//4
        assert A % 32 == 0
        tau = tau_of(A, d0, D)
        x, y = xy(tau)
        say(f'  base form [{A},{d0},1]  |y^2-x^3-4x| = {pari.precision(on_curve(x,y),20)}'.replace('\n',''))
        say(f'  x(z_n) = {pari.precision(x,30)}  y = {pari.precision(y,30)}')
        # (b) other deltas
        for d in ds[1:]:
            A2 = (n + d*d)//4
            x2, y2 = xy(tau_of(A2, d, D))
            same = abs(x2 - x) + abs(y2 - y)
            conj = abs(x2 - pari.conj(x)) + abs(y2 - pari.conj(y))
            say(f'  delta={d}: |P-P0|={float(same):.2e}  |P-conj P0|={float(conj):.2e}')
        # (c) algebraic degree of x
        reps = heegner_reps(D, d0)
        pts = {}
        for r, (a, b, c) in reps.items():
            pts[r] = xy(tau_of(a, b, D))
        xs = [pts[r][0] for r in pts] + [pari.conj(pts[r][0]) for r in pts]
        X = pari('X')
        P = pari(1)
        for v in xs:
            P *= (X - v)
        coeffs = [pari.real(P.polcoef(k)) for k in range(2*h + 1)]
        imax = max(abs(pari.imag(P.polcoef(k))) for k in range(2*h + 1))
        rc = [pari.round(c) for c in coeffs]
        err = max(abs(c - r) for c, r in zip(coeffs, rc))
        poly = pari.Pol(list(reversed(rc)), 'X')
        say(f'  prod over 2h Heegner x-coords: max imag part {float(imax):.1e}, dist to Z[X] {float(err):.1e}')
        say(f'  min poly candidate: {poly}  factor: {pari.factor(poly)[0]}'.replace('\n', ''))
        # is x(z_n) a root, and is the polynomial irreducible / which field?
        if 2*h <= 16 and err < 1e-50:
            nf = pari.polredabs(poly) if pari.polisirreducible(poly) else None
            say(f'  irreducible: {pari.polisirreducible(poly)}  polredabs: {nf}')
            if nf is not None:
                # compare with the Hilbert class field of Q(sqrt(-n)) (absolute)
                bnf = pari.bnfinit(pari(f'y^2+{n}'), 1)
                hcf = pari.bnrclassfield(bnf, 0, 2)   # absolute defining polynomial of H
                say(f'  Hilbert class field (polredabs): {pari.polredabs(hcf)}  same field: {pari.nfisisom(pari.polredabs(hcf), nf) != 0}')
        # (d) genus point: classes in the principal genus = squares in Cl
        forms = list(pts.keys())
        def qf(r): return pari.Qfb(*r)
        squares = set()
        for r in forms:
            s = pari.qfbred(qf(r)**2)
            squares.add(tuple(int(t) for t in pari.Vec(s)[:3]))
        sq = [r for r in forms if r in squares]
        say(f'  2Cl = {sq}  (g(n) = #2Cl = {len(sq)})')
        Zs = None
        for r in sq:
            Zs = pts[r] if Zs is None else add(Zs, pts[r])
        if Zs is None:
            say('  Z(n) = 0 (point at infinity)')
        else:
            say(f'  Z(n): x = {pari.precision(Zs[0],25)}  y = {pari.precision(Zs[1],25)}')
            for coord, nm in ((Zs[0], 'x'), (Zs[1], 'y')):
                g = len(set(squares)) and (h // len(sq))
                # degree of L_n over Q is 2*h/#2Cl
                dg = 2*h//len(sq)
                ad = pari.algdep(coord, dg)
                say(f'  algdep(Z.{nm}, {dg}) = {ad}  |res|={float(abs(pari.subst(ad, "x", coord))):.1e}')
    open('class7.out', 'w').write('\n'.join(out) + '\n')
