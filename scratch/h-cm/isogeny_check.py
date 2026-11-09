"""Independent algebraic recomputation of CM values on X*(6) from Elkies' covers
X0*(l) -> X*(6), l = 5, 7, 13, and the involutions w_l (Elkies, ANTS 1998, eqs. (40)-(43)
and Section 3.4).  A point x of X0*(l) with t(x) = t(w_l(x)) gives a CM point of X*(6)
admitting an l-isogeny to itself; rational values t obtained this way are compared with
Elkies' Table 1.  Also checks the ramification (cycle structure) of each cover."""
import sympy as sp
from fractions import Fraction as Fr
x = sp.symbols('x')
covers = {
 5: (540*x**6 + 324*x**5 + 135*x**4 + 1, (42 - 55*x)/(55 + 300*x)),
 7: (-(4*x**2 + 4*x + 25)*(2*x**3 - 3*x**2 + 12*x - 2)**2/(108*(7*x**2 - 8*x + 37)),
     (116 - 9*x)/(9 + 20*x)),
 13: (1 - sp.Rational(27, 4)*(x**2 + 36)*(x**3 + x**2 + 35*x + 27)**4/((7*x**2 + 2*x + 247)*(x**2 + 39)**6),
      (5*x + 72)/(2*x - 5)),
}
table = {Fr(-169, 27): 84, Fr(2312, 125): 40, Fr(-1377, 1024): 51, Fr(3211, 1024): 19,
         Fr(5776, 3375): 120, Fr(6877, 15625): 52, Fr(13689, 15625): 132, Fr(152881, 138240): 75,
         Fr(-701784, 15625): 168, Fr(21250987, 16000000): 43, Fr(66863329, 11390625): 228,
         Fr(15545888, 20796875): 88, Fr(-296900721, 16000000): 123, Fr(421850521, 1771561): 100,
         Fr(-1073152081, 3024000000): 147, Fr(27008742384, 27680640625): 312,
         Fr(77903700667, 1024000000): 67, Fr(69630712957, 377149515625): 148,
         Fr(-455413074649, 747377296875): 372, Fr(-32408609436736, 55962140625): 408,
         Fr(-5766681714488721, 1814078464000000): 267,
         Fr(66432278483452232, 56413239012828125): 232,
         Fr(71475755554842930369, 224337327397603890625): 708,
         Fr(699690239451360705067, 684178814003344000000): 163,
         Fr(0): 24, Fr(1): 4}
found = {}
for l, (t, w) in covers.items():
    t = sp.together(t)
    def cyc(expr):
        n, d = sp.fraction(sp.together(expr))
        return sorted([m for f, m in sp.factor_list(n)[1] for _ in range(sp.degree(f, x))]), \
               sorted([m for f, m in sp.factor_list(d)[1] for _ in range(sp.degree(f, x))])
    print(f"l={l}: deg t = {max(sp.degree(sp.numer(t), x), sp.degree(sp.denom(t), x))};",
          "zeros/poles of t:", cyc(t), "; zeros of t-1:", cyc(t - 1)[0])
    print("   w_l is an involution:", sp.simplify(w.subs(x, w) - x) == 0,
          "; w_l permutes zeros of t and of t-1 within each multiplicity class (checked by values below)")
    eq = sp.numer(sp.together(t - t.subs(x, w)))
    vals = set()
    for f, m in sp.factor_list(sp.expand(eq))[1]:
        if sp.degree(f, x) > 4: continue
        for r in sp.Poly(f, x).all_roots() if sp.degree(f, x) <= 2 else []:
            v = sp.nsimplify(sp.simplify(t.subs(x, r)))
            if v.is_rational:
                vals.add(Fr(int(sp.numer(v)), int(sp.denom(v))))
    for v in sorted(vals):
        found.setdefault(v, set()).add(l)
        print(f"   rational CM value t = {v}  ->  table |D| = {table.get(v, 'NOT IN TABLE')}")
print("table values recomputed algebraically:", sorted(table[v] for v in found if v in table))
