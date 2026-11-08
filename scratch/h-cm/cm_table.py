"""Part A: the manuscript's J in Elkies' coordinate t on X*(6).
Part B: Elkies' 27 rational CM points (ANTS 1998, Table 1; B = 125 for |D| = 40, see Table 2):
square classes of t and t-1, and rational roots of J(u) = j_D (factor the degree-12 polynomial).
Part C: consistency of the model Q(t)(sqrt(-t), sqrt(3(t-1))) of X(6) -> X*(6) and of the
reciprocity rule  Frob(p) = w_p  (p | 6 ramified in k) with every entry of the table."""
import sympy as sp
from fractions import Fraction as Fr

u = sp.symbols('u')
F = u*(u+15)*(u+20)*(u+24)*(u+30)*(u+60)
G = 7*u**2 + 300*u + 3600
H = (u**2 - 60*u - 1800)*(13*u**2 + 480*u + 3600)*(11*u**2 + 600*u + 7200)
J = -57600*F**2/G**6
print("== Part A")
print("G^6 - 97200 F^2 - H^2 =", sp.expand(G**6 - 97200*F**2 - H**2))
t_of_u = sp.simplify(1 + sp.Rational(27, 16)*J)
print("t(u) = 1 + 27 J/16 equals H^2/G^6:", sp.simplify(t_of_u - H**2/G**6) == 0)
print("t(u) - 1 equals -3 (180 F/G^3)^2:", sp.simplify(t_of_u - 1 + 3*(180*F/G**3)**2) == 0)
print("j at t = 1, oo, 0:", [sp.Rational(16, 27)*(tt - 1) for tt in (1, 0)], "and oo")

# (|D|, A, B, factorization of A-B claimed in Table 2 as dict) ; Table 1 of Elkies
T = [(84, -169, 27), (40, 2312, 125), (51, -1377, 1024), (19, 3211, 1024), (120, 5776, 3375),
     (52, 6877, 15625), (132, 13689, 15625), (75, 152881, 138240), (168, -701784, 15625),
     (43, 21250987, 16000000), (228, 66863329, 11390625), (88, 15545888, 20796875),
     (123, -296900721, 16000000), (100, 421850521, 1771561), (147, -1073152081, 3024000000),
     (312, 27008742384, 27680640625), (67, 77903700667, 1024000000),
     (148, 69630712957, 377149515625), (372, -455413074649, 747377296875),
     (408, -32408609436736, 55962140625), (267, -5766681714488721, 1814078464000000),
     (232, 66432278483452232, 56413239012828125),
     (708, 71475755554842930369, 224337327397603890625),
     (163, 699690239451360705067, 684178814003344000000)]
# |C| = |A - B| factorizations from Table 2
Cfac = {84: {2: 2, 7: 2}, 40: {3: 7}, 51: {7: 4}, 19: {3: 7}, 120: {7: 4}, 52: {2: 2, 3: 7},
        132: {2: 4, 11: 2}, 75: {11: 4}, 168: {11: 4, 7: 2}, 88: {3: 7, 7: 4}, 43: {3: 7, 7: 4},
        228: {2: 6, 7: 4, 19: 2}, 123: {7: 4, 19: 4}, 100: {2: 4, 3: 7, 7: 4, 5: 1},
        147: {11: 4, 23: 4}, 312: {7: 4, 23: 4}, 67: {3: 7, 7: 4, 11: 4},
        148: {2: 2, 3: 7, 7: 4, 11: 4}, 372: {2: 2, 7: 4, 19: 4, 31: 2},
        408: {7: 4, 11: 4, 31: 4}, 267: {7: 4, 31: 4, 43: 4}, 232: {3: 7, 7: 4, 11: 4, 19: 4},
        708: {2: 8, 7: 4, 11: 4, 47: 4, 59: 2}, 163: {3: 11, 7: 4, 19: 4, 23: 4}}

def sqf(q):
    """signed squarefree part of a nonzero rational"""
    q = Fr(q); n = q.numerator*q.denominator
    s = -1 if n < 0 else 1
    r = 1
    for p, e in sp.factorint(abs(n)).items():
        if e % 2: r *= p
    return s*r

print("\n== Part B")
print("Table 2 check (A-B factorization):",
      all(abs(A - B) == sp.prod([p**e for p, e in Cfac[d].items()]) for d, A, B in T))
cands = []
for d, A, B in T:
    t = Fr(A, B)
    sq_t, sq_t1 = sqf(t), sqf(t - 1)
    ok = (sq_t == 1 and sq_t1 == -3)
    P = sp.Poly(B*H**2 - A*G**6, u)
    fl = sp.factor_list(P.as_expr())[1]
    degs = sorted(sp.degree(f, u)*m for f, m in fl)
    roots = [r for r in sp.Poly(P).ground_roots()]
    print(f"|D|={d:4d} t={str(t):>48s} in(0,1)={0 < t < 1!s:5s} sqf(t)={sq_t:6d} "
          f"sqf(t-1)={sq_t1:6d} square-class test={ok!s:5s} factor degrees={degs} rational roots={roots}")
print("elliptic points: H, G have no rational roots:",
      [sp.Poly(f, u).ground_roots() for f in (H, G)])

print("\n== Part C (fibre field Q(sqrt(-t), sqrt(3(t-1))) and Frobenius at ramified p in {2,3})")
def prime_discs(D):
    """prime discriminants of a fundamental discriminant D"""
    out = []; m = D
    if m % 4 == 0:
        m //= 4
        if m % 2 == 0: out.append(8 if (m//2) % 4 == 1 else -8); m //= 2
        else: out.append(-4); 
    for p in sp.factorint(abs(m)):
        out.append(p if p % 4 == 1 else -p)
    assert sp.prod(out) == D, (D, out)
    return out
def kron(a, p):
    return sp.jacobi_symbol(a % p, p) if p > 2 else (0 if a % 2 == 0 else (1 if a % 8 in (1, 7) else -1))
# non-fundamental orders: generators of the ring class field (h = 2) over Q
special = {75: (-3, [-3, 5]), 100: (-4, [-4, 5]), 147: (-3, [-3, -7])}
W = {(1, -1): 'w2', (-1, -1): 'w3', (-1, 1): 'w6', (1, 1): 'id'}
allok = True
for d, A, B in T:
    t = Fr(A, B); s1, s2 = sqf(-t), sqf(3*(t - 1))
    if d in special:
        dK, gens = special[d]
    else:
        dK, gens = -d, prime_discs(-d)
    # express s1, s2 as products of the Kummer generators (mod squares)
    def express(s):
        for mask in range(1 << len(gens)):
            v = sp.prod([gens[i] for i in range(len(gens)) if mask >> i & 1])
            if sqf(v) == s: return mask
        return None
    e1, e2 = express(s1), express(s2)
    line = f"|D|={d:4d} s1={s1:6d} s2={s2:6d} in genus field: {e1 is not None and e2 is not None}"
    if e1 is None or e2 is None: allok = False
    cc = W[(1 if s1 > 0 else -1, 1 if s2 > 0 else -1)]
    line += f"  complex conj acts as {cc}"
    if cc == 'id': allok = False
    for p in (2, 3):
        if dK % p: continue  # p inert in k (split is impossible for an optimal embedding)
        # Frobenius of the prime above p on sqrt(g): chi_g(p) for p not dividing g; the generator
        # divisible by p is fixed by the requirement that sqrt(dK) (and sqrt(D)) be fixed.
        sg = []
        for g in gens:
            sg.append(kron(g, p) if g % p else None)
        i0 = [i for i, g in enumerate(gens) if g % p == 0]
        # product of signs over generators whose product is dK (or D) must be +1
        prod_others = sp.prod([sg[i] for i in range(len(gens)) if i not in i0 and (dK % gens[i] == 0 or d not in special)])
        for i in i0: sg[i] = prod_others if d not in special else 1
        act = lambda mask: sp.prod([sg[i] for i in range(len(gens)) if mask >> i & 1])
        a = (act(e1), act(e2))
        want = 'w2' if p == 2 else 'w3'
        got = W[a]
        line += f"  Frob(p{p}) acts as {got} (predicted {want})"
        if got != want: allok = False
    print(line)
print("all consistency checks pass:", allok)

print("\n== Part D (the fibre over a rational u, and the twist constants)")
I = sp.I
y1, y2 = I*H/G**3, 540*I*F/G**3
print("y1 = iH/G^3 satisfies y1^2 = -t(u):", sp.simplify(y1**2 + H**2/G**6) == 0)
print("y2 = 540iF/G^3 satisfies y2^2 = 3(t(u)-1):", sp.simplify(y2**2 - 3*(H**2/G**6 - 1)) == 0)
# twist constants c0, c1 with function field Q(t)(sqrt(c0 t), sqrt(c1 (t-1))): for a class number one
# discriminant D the fibre field must lie in Q(sqrt(D)); intersect over |D| = 19, 43, 67, 163
cands0, cands1 = None, None
for d, A, B in T:
    if d not in (19, 43, 67, 163): continue
    t = Fr(A, B); a, b = sqf(t), sqf(t - 1)
    c0 = {sqf(Fr(s, a)) for s in (1, -d)}; c1 = {sqf(Fr(s, b)) for s in (1, -d)}
    cands0 = c0 if cands0 is None else cands0 & c0
    cands1 = c1 if cands1 is None else cands1 & c1
    print(f"   |D|={d}: c0 in {sorted(c0)}, c1 in {sorted(c1)}")
print("forced: c0 =", cands0, " c1 =", cands1)
