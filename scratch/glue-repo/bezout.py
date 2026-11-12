"""Homogeneous Bezout certificates s_h*P_h + t_h*Q_h = N*b^d for (F,G), (F,H), (G,H).
Run: ~/pyenv/bin/python -I scratch/glue-repo/bezout.py"""
import sympy as sp
u, a, b = sp.symbols('u a b')
F = u*(u+15)*(u+20)*(u+24)*(u+30)*(u+60)
G = 7*u**2 + 300*u + 3600
H = (u**2-60*u-1800)*(13*u**2+480*u+3600)*(11*u**2+600*u+7200)
def hom(P, d): return sp.expand(sp.simplify(b**d * P.subs(u, a/b)))
for n1, P, n2, Q in [("F", F, "G", G), ("F", F, "H", H), ("G", G, "H", H)]:
    s, t, g = sp.gcdex(sp.Poly(P, u, domain='QQ'), sp.Poly(Q, u, domain='QQ'))
    den = sp.ilcm(*[c.q for c in s.all_coeffs() + t.all_coeffs()])
    s2, t2 = (s * den), (t * den)
    N = den  # s2*P + t2*Q = den
    cs = sp.igcd(*[int(c) for c in s2.all_coeffs() + t2.all_coeffs()])
    s2, t2, N = s2 * sp.Rational(1, cs), t2 * sp.Rational(1, cs), sp.Rational(N, cs)
    assert sp.expand(s2.as_expr()*P + t2.as_expr()*Q - N) == 0
    dP, dQ = sp.degree(P, u), sp.degree(Q, u)
    ds, dt = dQ - 1, dP - 1
    sh, th = hom(s2.as_expr(), ds), hom(t2.as_expr(), dt)
    d = dP + dQ - 1
    assert sp.expand(sh*hom(P, dP) + th*hom(Q, dQ) - N*b**d) == 0
    print(f"-- {n1},{n2}: N = {N} = {sp.factorint(N)}, b-power {d}")
    print(f"s_h = {sh}")
    print(f"t_h = {th}")
