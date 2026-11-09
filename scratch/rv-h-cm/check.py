"""Independent checks for the review of docs/research/h-cm.md.
A  manuscript identities (diophantine_zq.tex lines 377-386, 510-516, 908-909)
B  twist constants (c0, c1) from Shimura reciprocity at the elliptic points + X(R) empty
C  Elkies' covers X0*(l) -> X*(6), l = 5, 7, 13 (transcribed from the TeX source, eqs (X5),(X7(6)),(X13))
D  Elkies' tables 1-2: misprint, factorizations, square classes, rational roots of J(u) = j
E  count 2^b h(o) = 4, field of the fibre vs Gonzalez-Rotger Thm 5.12, Frobenius at ramified p
F  the lift P^1_u -> X^6 over Q(i): degree, ramification, Riemann-Hurwitz
G  effect of the alternative labelling (0 <-> oo swapped)"""
import sympy as sp
from fractions import Fraction as Fr
from itertools import product
u, x, T = sp.symbols('u x T')
F = u*(u+15)*(u+20)*(u+24)*(u+30)*(u+60)
G = 7*u**2 + 300*u + 3600
H = (u**2 - 60*u - 1800)*(13*u**2 + 480*u + 3600)*(11*u**2 + 600*u + 7200)
J = -57600*F**2/G**6

def sqf(q):
    q = Fr(q); n = q.numerator*q.denominator
    s = -1 if n < 0 else 1; r = 1
    for p, e in sp.factorint(abs(n)).items():
        if e % 2: r *= p
    return s*r

print("== A. identities")
print("G^6-97200F^2-H^2 == 0:", sp.expand(G**6 - 97200*F**2 - H**2) == 0)
t_u = sp.cancel(1 + sp.Rational(27, 16)*J)
print("1+27J/16 == H^2/G^6:", sp.cancel(t_u - H**2/G**6) == 0)
print("1+27J/16 - 1 == -3(180F/G^3)^2:", sp.cancel(t_u - 1 + 3*(180*F/G**3)**2) == 0)
print("Moebius t=1+27j/16 sends j=-16/27,0,oo to:", 1 + sp.Rational(27, 16)*sp.Rational(-16, 27), 1, "oo")
for f in [G, u**2 - 60*u - 1800, 13*u**2 + 480*u + 3600, 11*u**2 + 600*u + 7200]:
    d = sp.discriminant(f, u); print("  disc", f, "=", d, "=", sp.factorint(d), "square:", sp.sqrt(d).is_rational)
# fibre coordinates: y1^2 = -t, y2^2 = 3(t-1); y1 = i H/G^3, y2 = 540 i F/G^3
y1, y2 = sp.I*H/G**3, 540*sp.I*F/G**3
print("y1^2 + t(u) == 0:", sp.cancel(sp.expand(y1**2) + H**2/G**6) == 0,
      "; y2^2 - 3(t(u)-1) == 0:", sp.cancel(sp.expand(y2**2) - 3*(H**2/G**6 - 1)) == 0)
import random
random.seed(1)
for _ in range(5):
    uu = sp.Rational(random.randint(-500, 500), random.randint(1, 60))
    if uu in (0, -15, -20, -24, -30, -60): continue
    tt = t_u.subs(u, uu)
    print(f"  u={uu}: 0<t<1 {0 < tt < 1}; sqf(-t)={sqf(-tt)}, sqf(3(t-1))={sqf(3*(tt-1))}")

print("\n== B. twist constants")
# Q-quadratic subfields as squarefree d; a quadratic field Q(sqrt d) or Q when d = 1.
def quadfield_in(d, gens):
    """is sqrt(d) in the multiquadratic field Q(sqrt g : g in gens)?  (F2-span test on squarefree parts)"""
    span = {1}
    for g in gens:
        span |= {sqf(s*g) for s in span}
    return sqf(d) in span
sols = []
for c0, c1 in product([1, -1, 2, -2, 3, -3, 6, -6], repeat=2):
    # X(R) empty: no real t with c0 t > 0 and c1 (t-1) > 0, and fibres over 0, 1, oo not real
    real_pts = (c0 > 0 and c1 > 0) or (c0 < 0 and c1 < 0) or (c0 > 0 and c1 < 0)
    real_pts |= (-c1 > 0) or (c0 > 0) or (sqf(Fr(c1, c0)) > 0)
    # t = 0 (D=-24): residue field Q(sqrt(-c1)); K Q(x) must be H_{-24} = Q(sqrt-6, sqrt2)
    ok24 = sqf(-c1) != 1 and sqf(-c1) != -6 and quadfield_in(-c1, [-6, 2])
    # t = oo (D=-3): residue field Q(sqrt(c1/c0)) must be inside K = Q(sqrt-3) (h = 1), K Q(x) = K
    ok3 = quadfield_in(Fr(c1, c0), [-3])
    # t = 1 (D=-4): residue field Q(sqrt c0) inside K = Q(i)
    ok4 = quadfield_in(c0, [-1])
    if not real_pts and ok24 and ok3 and ok4:
        sols.append((c0, c1))
print("(c0,c1) mod squares (over {+-1,+-2,+-3,+-6}) compatible with X(R)=empty and reciprocity at t=0,1,oo:", sols)
sols2 = [(c0, c1) for c0, c1 in product([1, -1, 2, -2, 3, -3, 6, -6], repeat=2)
         if quadfield_in(-c1, [-6, 2]) and sqf(-c1) not in (1, -6) and quadfield_in(Fr(c1, c0), [-3])
         and sqf(Fr(c1, c0)) != 1]
print("  same, using only reciprocity (no real-points input):", sols2)

print("\n== C. Elkies' covers (from the TeX source)")
cov = {5: (540*x**6 + 324*x**5 + 135*x**4 + 1,
           [1 + 27*x**4*(20*x**2 + 12*x + 5), (15*x**2 - 6*x + 1)*(6*x**2 + 3*x + 1)**2],
           (42 - 55*x)/(55 + 300*x)),
       7: (-(4*x**2 + 4*x + 25)*(2*x**3 - 3*x**2 + 12*x - 2)**2/(108*(7*x**2 - 8*x + 37)),
           [1 - (2*x**2 - x + 8)**4/(108*(7*x**2 - 8*x + 37))],
           (116 - 9*x)/(9 + 20*x)),
       13: (1 - sp.Rational(27, 4)*(x**2 + 36)*(x**3 + x**2 + 35*x + 27)**4/((7*x**2 + 2*x + 247)*(x**2 + 39)**6),
            [(x**7 - 50*x**6 + 63*x**5 - 5040*x**4 + 783*x**3 - 168426*x**2 - 6831*x - 1864404)**2
             / (4*(7*x**2 + 2*x + 247)*(x**2 + 39)**6)],
            (5*x + 72)/(2*x - 5))}
table1 = [(3, 1, 0), (4, 1, 1), (24, 0, 1), (84, -169, 27), (40, 2312, 25), (51, -1377, 1024), (19, 3211, 1024),
          (120, 5776, 3375), (52, 6877, 15625), (132, 13689, 15625), (75, 152881, 138240),
          (168, -701784, 15625), (43, 21250987, 16000000), (228, 66863329, 11390625),
          (88, 15545888, 20796875), (123, -296900721, 16000000), (100, 421850521, 1771561),
          (147, -1073152081, 3024000000), (312, 27008742384, 27680640625),
          (67, 77903700667, 1024000000), (148, 69630712957, 377149515625),
          (372, -455413074649, 747377296875), (408, -32408609436736, 55962140625),
          (267, -5766681714488721, 1814078464000000), (232, 66432278483452232, 56413239012828125),
          (708, 71475755554842930369, 224337327397603890625),
          (163, 699690239451360705067, 684178814003344000000)]
proved = {3, 4, 24, 84, 40, 51, 19, 120, 52, 132, 75, 168, 43, 88, 100, 147, 312}  # 'Y' column
tval = {}
for D, A, B in table1:
    if D == 40: B = 125   # Table 2 and the text of section 3.4 give B = 5^3
    tval[D] = None if B == 0 else Fr(A, B)
inv = {v: D for D, v in tval.items() if v is not None}
def ram(expr):
    n, d = sp.fraction(sp.cancel(expr))
    dn, dd = sp.degree(n, x), sp.degree(d, x)
    zs = sorted(m for f, m in sp.factor_list(n)[1] for _ in range(sp.degree(f, x)))
    ps = sorted(m for f, m in sp.factor_list(d)[1] for _ in range(sp.degree(f, x)))
    if dn > dd: ps = sorted(ps + [dn - dd])
    if dd > dn: zs = sorted(zs + [dd - dn])
    return zs, ps
recomputed = set()
for l, (t, alts, w) in cov.items():
    t = sp.cancel(t)
    print(f"l={l}: alternative forms agree: {[sp.cancel(t - a) == 0 for a in alts]}")
    z0, pinf = ram(t); z1, _ = ram(t - 1)
    print(f"   over t=0: {z0}, t=1: {z1}, t=oo: {pinf}  (degree {sum(z0)}, expected {l+1})")
    print("   w_l involution:", sp.cancel(w.subs(x, w) - x) == 0,
          "; t(w_l(x)) for elliptic points:")
    n0 = [f for f, m in sp.factor_list(sp.numer(sp.cancel(t)))[1] if m == 1]
    n1 = [f for f, m in sp.factor_list(sp.numer(sp.cancel(t - 1)))[1] if m == 1]
    dI = [f for f, m in sp.factor_list(sp.denom(sp.cancel(t)))[1] if m == 1]
    for name, fs in (("simple zeros of t", n0), ("simple zeros of t-1", n1), ("simple poles of t", dI)):
        for f in fs:
            img = sp.numer(sp.cancel(f.subs(x, w)))
            print(f"     {name}: {f}; w_l maps roots to roots: {sp.rem(sp.Poly(img, x), sp.Poly(f, x)).is_zero}")
    # all CM points of X*(6) with an l-isogeny to themselves: t(x) = t(w x)
    eq = sp.numer(sp.cancel(t - t.subs(x, w)))
    for f, m in sp.factor_list(sp.expand(eq))[1]:
        dg = sp.degree(f, x)
        # value of t on the roots of f: rational iff t mod f is constant (as element of Q[x]/f)
        num, den = sp.fraction(sp.cancel(t))
        P = sp.Poly(f, x)
        try:
            dinv = sp.invert(sp.Poly(den, x), P)
        except Exception:
            continue
        r = sp.rem(sp.Poly(num, x)*dinv, P)
        if r.degree() <= 0:
            v = r.as_expr()
            fv = Fr(int(sp.numer(v)), int(sp.denom(v)))
            recomputed.add(fv)
            print(f"     factor of degree {dg}: t = {fv} -> |D| = {inv.get(fv, 'NOT IN TABLE')}")
        else:
            print(f"     factor of degree {dg}: t irrational on its roots")
    for xx in ({5: [sp.oo, 0], 7: [sp.oo]}.get(l, [])):  # special points: x=oo (D=-3), x=0 on X0*(5) (D=-4)
        wx = sp.limit(w, x, xx) if xx == sp.oo else w.subs(x, xx)
        v = sp.nsimplify(t.subs(x, wx)); fv = Fr(int(sp.numer(v)), int(sp.denom(v)))
        recomputed.add(fv)
        print(f"     w_{l}({xx}) = {wx}: t = {fv} -> |D| = {inv.get(fv, 'NOT IN TABLE')}")
rec = sorted(inv[v] for v in recomputed if v in inv)
print("table entries recomputed from the covers:", rec)
print("proved ('Y') entries not recomputed:", sorted(proved - set(rec) - {3}))

print("\n== D. Table 2 factorizations, square classes, rational roots")
tab2 = {84: ({13: 2}, {3: 3}, {2: 2, 7: 2}), 40: ({2: 3, 17: 2}, {5: 3}, {3: 7}),
        51: ({3: 4, 17: 1}, {2: 10}, {7: 4}), 19: ({13: 2, 19: 1}, {2: 10}, {3: 7}),
        120: ({2: 4, 19: 2}, {3: 3, 5: 3}, {7: 4}), 52: ({23: 2, 13: 1}, {5: 6}, {2: 2, 3: 7}),
        132: ({3: 4, 13: 2}, {5: 6}, {2: 4, 11: 2}), 75: ({17: 2, 23: 2}, {2: 10, 3: 3, 5: 1}, {11: 4}),
        168: ({2: 3, 3: 5, 19: 2}, {5: 6}, {11: 4, 7: 2}), 88: ({2: 5, 17: 2, 41: 2}, {5: 6, 11: 3}, {3: 7, 7: 4}),
        43: ({19: 2, 37: 2, 43: 1}, {2: 10, 5: 6}, {3: 7, 7: 4}),
        228: ({13: 2, 17: 2, 37: 2}, {3: 6, 5: 6}, {2: 6, 7: 4, 19: 2}),
        123: ({3: 4, 13: 2, 23: 2, 41: 1}, {2: 10, 5: 6}, {7: 4, 19: 4}),
        100: ({19: 2, 23: 2, 47: 2}, {11: 6}, {2: 4, 3: 7, 7: 4, 5: 1}),
        147: ({17: 2, 41: 2, 47: 2}, {2: 10, 3: 3, 5: 6, 7: 1}, {11: 4, 23: 4}),
        312: ({2: 4, 3: 5, 17: 2, 43: 2, 13: 1}, {5: 6, 11: 6}, {7: 4, 23: 4}),
        67: ({13: 2, 43: 2, 61: 2, 67: 1}, {2: 16, 5: 6}, {3: 7, 7: 4, 11: 4}),
        148: ({13: 2, 47: 2, 71: 2, 37: 1}, {5: 6, 17: 6}, {2: 2, 3: 7, 7: 4, 11: 4}),
        372: ({13: 2, 23: 2, 37: 2, 61: 2}, {3: 3, 5: 6, 11: 6}, {2: 2, 7: 4, 19: 4, 31: 2}),
        408: ({2: 6, 13: 2, 19: 2, 43: 2, 67: 2}, {3: 6, 5: 6, 17: 3}, {7: 4, 11: 4, 31: 4}),
        267: ({3: 6, 13: 2, 17: 2, 19: 2, 71: 2, 89: 1}, {2: 16, 5: 6, 11: 6}, {7: 4, 31: 4, 43: 4}),
        232: ({2: 3, 13: 2, 17: 2, 41: 2, 89: 2, 113: 2}, {5: 6, 23: 6, 29: 3}, {3: 7, 7: 4, 11: 4, 19: 4}),
        708: ({3: 4, 13: 2, 19: 2, 23: 2, 37: 2, 41: 2, 109: 2}, {5: 6, 17: 6, 29: 6}, {2: 8, 7: 4, 11: 4, 47: 4, 59: 2}),
        163: ({13: 2, 67: 2, 109: 2, 139: 2, 157: 2, 163: 1}, {2: 10, 5: 6, 11: 6, 17: 6}, {3: 11, 7: 4, 19: 4, 23: 4})}
bad = []
for D, A, B in table1[3:]:
    a, b, c = tab2[D]
    okA = sp.factorint(abs(A)) == a; okB = sp.factorint(B) == b; okC = sp.factorint(abs(A - B)) == c
    if not (okA and okB and okC): bad.append((D, okA, okB, okC))
print("Table 1 rows (as printed) disagreeing with Table 2 (|A|,B,|C| ok?):", bad)
print("|D|=40 with B=125: A-B =", 2312 - 125, "=", sp.factorint(2312 - 125))
npass = 0
for D in tval:
    t0 = tval[D]
    if t0 is None or t0 in (0, 1): continue
    passes = sqf(t0) == 1 and sqf(t0 - 1) == -3
    npass += passes
    a, b = t0.numerator, t0.denominator
    j = Fr(16, 27)*(t0 - 1)
    poly = sp.Poly(b*H**2 - a*G**6, u)
    degs = sorted(sp.degree(f, u) for f, m in sp.factor_list(poly.as_expr())[1] for _ in range(m))
    poly2 = sp.Poly(-57600*j.denominator*F**2 - j.numerator*G**6, u)
    same = sp.cancel(poly.as_expr()/poly2.as_expr()).is_number
    print(f"  |D|={D}: j={j}; square-class test passes: {passes}; factor degrees {degs}; matches line-950 polynomial: {same}")
print("rows passing the square-class test:", npass)

print("\n== E. counts, fibre fields, Frobenius at ramified primes")
def hform(Dn):  # class number of discriminant Dn < 0 (primitive reduced forms)
    h = 0; a = 1
    while 3*a*a <= -Dn:
        for b in range(-a + 1, a + 1):
            if (b*b - Dn) % (4*a): continue
            c = (b*b - Dn)//(4*a)
            if c < a or (c == a and b < 0): continue
            if sp.gcd(sp.gcd(a, b), c) == 1: h += 1
        a += 1
    return h
def kron(d, p):  # Kronecker symbol (d/p), p prime
    return sp.jacobi_symbol(d % p, p) if p != 2 else (0 if d % 2 == 0 else (1 if d % 8 in (1, 7) else -1))
for D in sorted(tval, key=lambda d: (tval[d] is None, d)):
    Dn = -D
    dK = sp.core.numbers.igcd(1, 1)
    d0 = sqf(Dn); dK = d0 if d0 % 4 == 1 else 4*d0
    f = sp.sqrt(sp.Rational(Dn, dK)); f = int(f)
    sym = {p: kron(dK, p) for p in (2, 3)}
    b = sum(1 for p in (2, 3) if sym[p] == -1)
    emb = all(sym[p] != 1 for p in (2, 3)) and sp.gcd(f, 6) == 1
    h = hform(Dn)
    t0 = tval[D]
    line = f"  |D|={D}: dK={dK}, f={f}, (dK/2),(dK/3)={sym[2]},{sym[3]}, emb ok {emb}, b={b}, h={h}, 2^b h={2**b*h}"
    if t0 is not None and t0 not in (0, 1):
        cls = sorted({sqf(-t0), sqf(3*(t0 - 1)), sqf(-3*t0*(t0 - 1))} - {1})
        deg = 2 if len(cls) == 1 else 4
        # genus field generators: p* for odd p | D, and -4, 8, -8 parts at 2
        gens = [p if p % 4 == 1 else -p for p in sp.factorint(D) if p % 2]
        if D % 2 == 0:
            rest = sqf(Fr(dK if f == 1 else Dn, 1))
            # 2-part: quotient of dK by odd prime discriminants
            odd = 1
            for g in [p if p % 4 == 1 else -p for p in sp.factorint(dK) if p % 2]: odd *= g
            gens.append(sqf(Fr(dK, odd)))
        in_genus = all(quadfield_in(c, gens) for c in cls)
        hasK = quadfield_in(d0, cls)
        if b == 2: pred = f"= K: {cls == [d0]}"
        elif b == 1: pred = f"= H_R (degree 4, contains K): {deg == 4 and hasK and in_genus}"
        else: pred = f"index 2 in H_R, not containing K: {deg == 4 and not hasK and in_genus}"
        line += f"; fibre classes {cls}; GR 5.12 prediction {pred}"
        # Frobenius at the prime above ramified p in {2,3}: sigma(sqrt d) = (d'/p) sqrt d, d' = d or d*dK prime to p
        fr = []
        for p in (2, 3):
            if sym[p] != 0: continue
            sg = []
            for d in (-t0, 3*(t0 - 1)):
                dd = sqf(d)
                if dd % p == 0 or (p == 2 and dd % 4 != 1):
                    for cand in (sqf(dd*d0), sqf(dd*d0)):
                        dd = cand
                if p == 2 and dd % 4 != 1:
                    sg.append('?'); continue
                sg.append(kron(dd, p))
            want = {2: [1, -1], 3: [-1, -1]}[p]
            fr.append(f"Frob_{p} on (y1,y2) = {sg} vs w_{p} {want}: {sg == want}")
        line += "; " + "; ".join(fr)
    print(line)

print("\n== F. the lift P^1_u -> X^6 over Q(i)")
# phi(u) = (y1, y2) = (i H/G^3, 540 i F/G^3) on the conic y2^2 + 3 y1^2 + 3 = 0
print("conic identity y2^2 + 3 y1^2 + 3 == 0:", sp.cancel(sp.expand(y2**2 + 3*y1**2 + 3)) == 0)
# rational parametrization of the conic over Q(i): point (y1,y2)=(i,0); s = y2/(y1 - i)
s = sp.cancel(sp.expand(y2/(y1 - sp.I)))
ns, ds = sp.fraction(s)
print("phi in the coordinate s = y2/(y1-i): degree", max(sp.degree(sp.expand(ns), u), sp.degree(sp.expand(ds), u)))
print("Riemann-Hurwitz for degree 3, totally ramified over two points: -2 == 3*(-2) + 2*2:", -2 == 3*(-2) + 2*2)

print("\n== G. alternative labelling j=0 <-> D=-3, j=oo <-> D=-4")
t_alt = sp.cancel(1 + sp.Rational(16, 27)/J)
print("t_alt(u) =", sp.factor(t_alt))
for uu in [1, 2, 5, sp.Rational(-1500, 61)]:
    tt = t_alt.subs(u, uu)
    print(f"  u={uu}: classes of -t, 3(t-1): {sqf(-tt)}, {sqf(3*(tt-1))}")
