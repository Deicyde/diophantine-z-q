# Symbolic check of the witness table of Lemma T (place 2, d = 5 mod 8) and of the torsion witnesses,
# plus a numeric check that every listed quotient is 4^m * (2-adic unit = 1 mod 8) for d = 5 mod 8.
import sympy as sp
from fractions import Fraction as F
d = sp.symbols('d')
rows = [  # (a, b, x, expected x/a, (x-d)/b, (x+d)/(ab))
 (d, 2, d, 1, 0, 1),
 (sp.Integer(-1), -d, sp.Integer(0), 0, 1, 1),
 (-d, -2*d, -d, 1, 1, 0),
 (1, 5, sp.Rational(1,4), sp.Rational(1,4), (1-4*d)/20, (1+4*d)/20),
 (d, 10, d*(1+4*d)/(1-4*d), (1+4*d)/(1-4*d), (2*d)**2/(5*(1-4*d)), 1/(5*(1-4*d))),
 (-1, -5*d, -4*d**2, (2*d)**2, (1+4*d)/5, (1-4*d)/5),
 (-d, -10*d, -d*(1-4*d)/(1+4*d), (1-4*d)/(1+4*d), 1/(5*(1+4*d)), 4/(5*(1+4*d))),
]
ok = True
for a, b, x, q1, q2, q3 in rows:
    for got, exp in ((x/a, q1), ((x-d)/b, q2), ((x+d)/(a*b), q3)):
        if sp.simplify(got - exp) != 0: ok = False; print("FAIL", a, b, got, exp)
print("symbolic table:", "ok" if ok else "FAIL")
def sq2(r):
    r = F(r)
    if r == 0: return True
    n, m, k = r.numerator, r.denominator, 0
    while n % 2 == 0: n //= 2; k += 1
    while m % 2 == 0: m //= 2; k -= 1
    return k % 2 == 0 and (n * pow(m, -1, 8)) % 8 == 1
bad = 0
for dv in range(5, 2000, 8):
    for a, b, x, q1, q2, q3 in rows:
        for q in (q1, q2, q3):
            r = sp.Rational(sp.sympify(q).subs(d, sp.Integer(dv))); val = F(int(r.p), int(r.q))
            if not sq2(val): bad += 1
print("numeric squares in Q2 for 250 values d = 5 mod 8: failures", bad)
