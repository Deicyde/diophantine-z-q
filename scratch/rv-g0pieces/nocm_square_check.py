"""Necessary condition for a rational CM value t_D of Elkies' coordinate t = 1 + 27 J/16 on X*(6)
to equal t(u) for some rational u: t(u) = (H/G^3)^2 and 1 - t(u) = 3 (180 F/G^3)^2
(since G^6 - 97200 F^2 = H^2, 97200 = 3*180^2). Rows re-entered from scratch/rv-nocm/nocm_check.py."""
from fractions import Fraction as Fr
from math import isqrt
import sympy as sp
ROWS = [
    (84, Fr(-169, 27)), (40, Fr(2312, 125)), (51, Fr(-1377, 1024)), (19, Fr(3211, 1024)),
    (120, Fr(5776, 3375)), (52, Fr(6877, 15625)), (132, Fr(13689, 15625)),
    (75, Fr(152881, 138240)), (168, Fr(-701784, 15625)), (43, Fr(21250987, 16000000)),
    (228, Fr(66863329, 11390625)), (88, Fr(15545888, 20796875)),
    (123, Fr(-296900721, 16000000)), (100, Fr(421850521, 1771561)),
    (147, Fr(-1073152081, 3024000000)), (312, Fr(27008742384, 27680640625)),
    (67, Fr(77903700667, 1024000000)), (148, Fr(69630712957, 377149515625)),
    (372, Fr(-455413074649, 747377296875)), (408, Fr(-32408609436736, 55962140625)),
    (267, Fr(-5766681714488721, 1814078464000000)),
    (232, Fr(66432278483452232, 56413239012828125)),
    (708, Fr(71475755554842930369, 224337327397603890625)),
    (163, Fr(699690239451360705067, 684178814003344000000)),
]
def issq(q):
    q = Fr(q)
    if q < 0: return False
    return isqrt(q.numerator)**2 == q.numerator and isqrt(q.denominator)**2 == q.denominator
u = sp.symbols('u')
F = u*(u+15)*(u+20)*(u+24)*(u+30)*(u+60)
G = 7*u**2 + 300*u + 3600
H = (u**2-60*u-1800)*(13*u**2+480*u+3600)*(11*u**2+600*u+7200)
assert sp.expand(G**6 - 97200*F**2 - H**2) == 0
J = -57600*F**2/G**6
assert sp.simplify(1 + sp.Rational(27,16)*J - H**2/G**6) == 0
hits = []
for D, t in ROWS:
    a, b = issq(t), issq((1 - t) / 3)
    print(D, t, "t square:", a, "(1-t)/3 square:", b)
    if a and b: hits.append((D, t))
    # exact: rational roots of H^2 - t G^6 (t = t(u))
    p = sp.Poly(sp.numer(sp.together(H**2 - sp.Rational(t.numerator, t.denominator)*G**6)), u)
    rr = [r for r in sp.roots(p, filter='Q')]
    assert rr == [], (D, rr)
print("rows passing the necessary condition:", hits)
print("rational roots of H^2 - t_D G^6: none for all 24 rows (asserted)")
# elliptic points: t = 0 (D=-24): H(u)=0; t = 1 (D=-4): F(u)=0; t = inf (D=-3): G(u)=0
print("rational roots of H:", sp.roots(sp.Poly(H, u), filter='Q'))
print("rational roots of F:", sp.roots(sp.Poly(F, u), filter='Q'))
print("rational roots of G:", sp.roots(sp.Poly(G, u), filter='Q'))
