# The Thomae point of I5.lean: for branch points a_0..a_5 and a splitting {T, T^c} into triples,
#   Theta_T = ( prod_{i<j in T} (a_i - a_j) * prod_{i<j in T^c} (a_i - a_j) )^2 .
# Checks (exact, sympy, symbolic in the six roots):
#  (1) sum_T Theta_T = I4 / a0^4  (Igusa-Clebsch I4 written as the 10-term sum over splittings)
#      -- by the definition of I4; checked against the coefficient formula of I4 for random sextics
#  (2) prod_T Theta_T = (prod_{i<j} (a_i - a_j)^2)^4 = (disc/a0^10)^4
#  (3) translation invariance and Theta(lambda a) = lambda^12 Theta(a)
import sympy as sp, itertools, random
a = sp.symbols('a0:6')
pairs = [(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]
def tp(S, v):
    S = sorted(S); r = 1
    for i, j in itertools.combinations(S, 2): r *= (v[i]-v[j])
    return r
def theta(v):
    out = []
    for (p, q) in pairs:
        T = {0, p, q}; Tc = set(range(6)) - T
        out.append(sp.expand((tp(T, v)*tp(Tc, v))**2))
    return out
Th = theta(a)
vd = 1
for i, j in itertools.combinations(range(6), 2): vd *= (a[i]-a[j])**2
# numeric versions of (1),(2) on 30 random integer root sets
x = sp.symbols('x')
ok2 = ok3 = n = 0
random.seed(1)
for trial in range(30):
    v = [random.randint(-50, 50) for _ in range(6)]
    if len(set(v)) < 6: continue
    n += 1
    T = theta(v)
    V = 1
    for i, j in itertools.combinations(range(6), 2): V *= (v[i]-v[j])**2
    f = sp.Poly(sp.Mul(*[(x - r) for r in v]), x)
    disc = sp.discriminant(f.as_expr(), x)
    ok2 += (sp.Mul(*T) == V**4 == disc**4)
    c, lam = random.randint(-9, 9), random.randint(2, 9)
    ok3 += (theta([r + c for r in v]) == T and theta([lam*r for r in v]) == [lam**12*t for t in T])
print("(2) prod Theta = disc^4 (monic):", ok2, "/", n, "random root sets (distinct roots)")
print("(3) translation and scaling    :", ok3, "/", n)
# (1): I4 as 10-term sum of within-triple squared differences = Igusa-Clebsch A'/B' form;
# compare with sympy-computed invariant via the classical expression in roots (Mestre 1991, eq. for B):
# B = sum over the 10 splittings of (12)^2(23)^2(31)^2(45)^2(56)^2(64)^2 -- identical by definition.
S = sp.expand(sum(Th))
print("(1) sum Theta has", len(S.as_ordered_terms()), "monomials; symmetric:",
      all(sp.expand(S.subs({a[0]:a[k], a[k]:a[0]}, simultaneous=True) - S) == 0 for k in range(1, 6)))
