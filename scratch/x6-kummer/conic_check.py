"""x6-kummer: consistency checks of the conic model C : Y^2 + 3X^2 + 3Z^2 = 0, pi = -16(X^2+Z^2)/(27 Z^2).
Run: ~/pyenv/bin/python -I scratch/x6-kummer/conic_check.py"""
import sympy as sp
import cypari2
pari = cypari2.Pari()

X, Y, Z, lam = sp.symbols('X Y Z lam')
C = Y**2 + 3*X**2 + 3*Z**2

def jval(pt):
    x, y, z = pt
    return sp.oo if z == 0 else sp.nsimplify(sp.simplify(-16*(x**2 + z**2)/(27*z**2)))

def fixed_points(sx, sy):
    """projective points [x:y:z] of C with [sx*x : sy*y : z] = [x:y:z]"""
    pts = set()
    for l in (1, -1):
        # sx*x = l*x, sy*y = l*y, z = l*z
        eqs = []
        for c, s in ((X, sx), (Y, sy), (Z, 1)):
            if s != l:
                eqs.append(c)
        for chart in (Z, X, Y):
            sols = sp.solve(eqs + [C, chart - 1], [X, Y, Z], dict=True)
            for so in sols:
                pt = tuple(sp.simplify(so.get(v, v)) for v in (X, Y, Z))
                if all(not c.free_symbols for c in pt):
                    # normalise
                    for k in (2, 0, 1):
                        if pt[k] != 0:
                            pt = tuple(sp.simplify(c/pt[k]) for c in pt); break
                    pts.add(pt)
    return pts

for name, (sx, sy) in {'X->-X (w6)': (-1, 1), 'Y->-Y (w2)': (1, -1), '(X,Y)->(-X,-Y) (w3)': (-1, -1)}.items():
    fp = fixed_points(sx, sy)
    print(name, 'fixed points:', sorted(map(str, fp)), 'j-values:', {str(jval(p)) for p in fp})

# Hilbert symbols: C <-> Y^2 = (-3) X^2 + (-3) Z^2 <-> (-3,-3); Kurihara x^2+y^2+3=0 <-> (-1,-3)
for (a, b) in ((-3, -3), (-1, -3)):
    print(f'({a},{b}) Hilbert symbols at 2,3,5,7,oo:',
          [int(pari.hilbert(a, b, p)) for p in (2, 3, 5, 7)], int(pari.hilbert(a, b, 0)))

# t = 1 + 27 j/16 at j = 0, -16/27 ; j = 16 (t-1)/27 = -16 (X^2+1)/27 with t = -X^2
j = sp.symbols('j')
t = 1 + sp.Rational(27, 16)*j
print('t(0) =', t.subs(j, 0), ' t(-16/27) =', t.subs(j, sp.Rational(-16, 27)))
print('16(t-1)/27 with t=-X^2 equals -16(X^2+1)/27:',
      sp.simplify(sp.Rational(16, 27)*(-X**2 - 1) - (-16*(X**2 + 1)/27)) == 0)

# fibre over sample rational j0: the four points (+-a, +-b), a^2=-t0, b^2=3(t0-1), lie on C, have pi=j0
for j0 in (sp.Rational(1), sp.Rational(-1), sp.Rational(5, 7), sp.Rational(16, 27), sp.Rational(-3, 2)):
    t0 = 1 + sp.Rational(27, 16)*j0
    a, b = sp.sqrt(-t0), sp.sqrt(3*(t0 - 1))
    pts = [(s1*a, s2*b, 1) for s1 in (1, -1) for s2 in (1, -1)]
    ok = all(sp.simplify(C.subs({X: p[0], Y: p[1], Z: 1})) == 0 and sp.simplify(jval(p) - j0) == 0 for p in pts)
    deg = pari(f'polcompositum(x^2+({t0}), x^2-3*(({t0})-1))')
    degs = [int(pari.poldegree(f)) for f in deg]
    print(f'j0={j0}: t0={t0}, four points on C with pi=j0: {ok}, distinct: {len(set(pts))==4}, '
          f'compositum degrees {degs}')
