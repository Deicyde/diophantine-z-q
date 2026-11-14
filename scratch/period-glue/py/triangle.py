"""period-glue: a (2,4,6) triangle presentation of Gamma*/Q^x inside N_B(O)^+.
Search: g4 = 1+i+j (fixes sqrt2+i), g2 in N(O) with trd = 0 and small coordinates, such that g2*g4 is elliptic of
order 6 in PSL2 (trd^2/nrd = 3); then g6 = (g2 g4)^{-1} up to scalars. Also report the rotation angles.
Run: ~/pyenv/bin/python -I triangle.py"""
import sympy as sp, itertools, mpmath as mp
R_ = sp.Rational
def qmul(x, y):
    a1,b1,c1,d1 = x; a2,b2,c2,d2 = y
    return (a1*a2 + 2*b1*b2 - 3*c1*c2 + 6*d1*d2, a1*b2 + b1*a2 + 3*(c1*d2 - d1*c2),
            a1*c2 + c1*a2 + 2*(b1*d2 - d1*b2), a1*d2 + d1*a2 + b1*c2 - c1*b2)
def nrd(x): a,b,c,d = x; return a*a - 2*b*b + 3*c*c - 6*d*d
def conj(x): a,b,c,d = x; return (a,-b,-c,-d)
basis = [(1,0,0,0), (0,1,0,0), (R_(1,2),0,R_(1,2),0), (0,R_(1,2),0,R_(1,2))]
Bm = sp.Matrix([[sp.nsimplify(t) for t in b] for b in basis]).T
def inO(x): return all(t.is_integer for t in Bm.solve(sp.Matrix([sp.nsimplify(t) for t in x])))
def vec(n): return tuple(sum(R_(n[k])*sp.nsimplify(basis[k][t]) for k in range(4)) for t in range(4))
def normalizes(x):
    N = nrd(x)
    if N == 0: return False
    xi = tuple(sp.nsimplify(t)/N for t in conj(x))
    return all(inO(qmul(qmul(x, b), xi)) and inO(qmul(qmul(xi, b), x)) for b in basis)
def iotaN(x):
    s = mp.sqrt(2); x0,x1,x2,x3 = [mp.mpf(sp.Rational(t).p)/sp.Rational(t).q for t in x]
    return mp.matrix([[x0 + x1*s, -3*x2 - 3*s*x3], [x2 - s*x3, x0 - x1*s]])
def fixpt(x):
    g = iotaN(x); a,b,c,d = g[0,0], g[0,1], g[1,0], g[1,1]
    disc = (a+d)**2 - 4*(a*d-b*c)
    z = ((a-d) + mp.sqrt(disc))/(2*c)
    return z if mp.im(z) > 0 else ((a-d) - mp.sqrt(disc))/(2*c)
g4 = (1,1,1,0)
print("g4 =", g4, "nrd", nrd(g4), "normalizes", normalizes(g4), "fixpt", fixpt(g4))
found = []
for n in itertools.product(range(-6,7), repeat=4):
    x = vec(n)
    if x[0] != 0 or nrd(x) <= 0: continue
    if nrd(x) not in (1,2,3,6): continue
    if not normalizes(x): continue
    for gg in (g4, conj(g4)):
      p = qmul(x, gg)
      t2 = (2*p[0])**2 / nrd(p)
      if t2 == 3:
        found.append(x)
        print("with", gg, ":", "g2 =", x, "nrd", nrd(x), "fix", mp.nstr(fixpt(x), 8), "| g2*g4 =", p, "nrd", nrd(p), "fix", mp.nstr(fixpt(p), 8))
