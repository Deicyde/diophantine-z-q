"""Extension checks for the review rv-h-b1 of route B1 (h-b1.md).
Run: ~/pyenv/bin/python -I scratch/rv-h-b1/rv_checks.py > scratch/rv-h-b1/rv_checks.output.txt
Sections:
 R1. O = Z<1,i,(1+j)/2,(i+ij)/2> in B=(2,-3) is a maximal order (disc 6); N5's polarization datum
 R2. ALL elliptic elements of the normalizer (primitive x in O, nrd in {1,2,3,6}, finite order in
     B^*/Q^*): their (trd,nrd), the CM order Q(x) cap O, its discriminant, W-image
 R3. Euler characteristics / Riemann-Hurwitz: (2,4,6) triangle group, X_6 -> P^1_j, components of Y_3
 R4. |Gamma'| = 144 recomputed group-theoretically: Zhat^* image, (O/3O)^1, component stabiliser 72
 R5. counterexample F1 = quadratic twist by p of a cover with no vertical ramification;
     the fibres over its branch points are unramified at p, so step 2 of Lemma NV alone does not
     exclude vertical ramification there; step 4 (distinct W-images) is what F1 lacks
 R6. neatness of K_3: no elliptic element of N lies in Q^* K_3 unless central
"""
from fractions import Fraction as Fr
from itertools import product
from math import gcd
import sympy
import cypari2
pari = cypari2.Pari()

a, b = 2, -3   # i^2 = 2, j^2 = -3 (same convention as scratch/h-b1/b1_checks.py)
def mul(x, y):
    x0,x1,x2,x3 = x; y0,y1,y2,y3 = y
    return (x0*y0 + a*x1*y1 + b*x2*y2 - a*b*x3*y3,
            x0*y1 + x1*y0 - b*x2*y3 + b*x3*y2,
            x0*y2 + x2*y0 + a*x1*y3 - a*x3*y1,
            x0*y3 + x3*y0 + x1*y2 - x2*y1)
def conj(x): return (x[0], -x[1], -x[2], -x[3])
def nrd(x): return x[0]*x[0] - a*x[1]*x[1] - b*x[2]*x[2] + a*b*x[3]*x[3]
def trd(x): return 2*x[0]
def add(x, y): return tuple(s+t for s, t in zip(x, y))
def scal(c, x): return tuple(c*s for s in x)
basis = [(Fr(1),Fr(0),Fr(0),Fr(0)),(Fr(0),Fr(1),Fr(0),Fr(0)),(Fr(1,2),Fr(0),Fr(1,2),Fr(0)),(Fr(0),Fr(1,2),Fr(0),Fr(1,2))]
Bm = sympy.Matrix([[sympy.Rational(basis[t][s]) for t in range(4)] for s in range(4)])
Binv = Bm.inv()
def coords_q(x): return list(Binv*sympy.Matrix([sympy.Rational(c) for c in x]))
def inO(x): return all(c.q == 1 for c in coords_q(x))
def elt(c): return tuple(sum(Fr(c[t])*basis[t][s] for t in range(4)) for s in range(4))

print("== R1. maximality of O and N5's polarization datum")
T = sympy.Matrix(4, 4, lambda r, s: sympy.Rational(trd(mul(basis[r], basis[s]))))
d = T.det()
print("det(trd(e_r e_s)) =", d, "= (disc O)^2 with disc O =", sympy.sqrt(abs(d)))
print("Hilbert symbols (2,-3)_p for p in 2,3,5,7,oo:", [int(pari.hilbert(2, -3, p)) for p in (2, 3, 5, 7)], int(pari.hilbert(2, -3, 0)))
print("=> B ramified exactly at {2,3}, disc(B)=6, and disc(O)=6: O is maximal:", abs(d) == 36)
mu = add(scal(2, (0,0,1,0)), (0,0,0,1))     # mu = 2j + ij
print("mu = 2j+ij: mu^2 =", mul(mu, mu), " (expect -6)")
muinv = scal(Fr(1, nrd(mu)), conj(mu))
P = sympy.Matrix(4, 4, lambda r, s: sympy.Rational(trd(mul(mul(muinv, basis[r]), conj(basis[s])))))
print("Trd(mu^-1 x ybar) matrix:", P.tolist(), " det:", P.det())

print("\n== R2. all elliptic elements of the normalizer, up to Q^*")
# primitive x in O with nrd n in {1,2,3,6} (normalizer reps: at split primes N = Q^* O^*, at 2,3 any unit
# of B_p normalizes the unique maximal order), of finite order mod Q^*: x^k in Q, x not in Q.
types = {}
R = 6
for c in product(range(-R, R+1), repeat=4):
    if all(t == 0 for t in c): continue
    if gcd(gcd(c[0], c[1]), gcd(c[2], c[3])) != 1: continue
    x = elt(c); n = nrd(x); t = trd(x)
    assert n.denominator == 1 and t.denominator == 1; n = int(n); t = int(t)
    if n not in (1, 2, 3, 6): continue
    if x[1] == 0 and x[2] == 0 and x[3] == 0: continue
    # finite order mod Q^*  <=>  t^2/n in {0,1,2,3}
    if Fr(t*t, n) not in (0, 1, 2, 3): continue
    D = int(t*t - 4*n)
    key = (abs(int(t)), int(n))
    if key in types: continue
    # CM order Q(x) cap O: largest f with (s + x)/f in O for some integer s
    best = 1
    for f in (2, 3, 4, 6):
        for s in range(f):
            if inO(scal(Fr(1, f), add((Fr(s),0,0,0), x))): best = max(best, f)
    Dorder = D // (best*best)
    order_k = {0: 2, 1: 6, 2: 4, 3: 6}[int(Fr(t*t, n))]   # order in B^*/Q^*: t^2/n = 4cos^2(pi/k)
    # x in normalizer? check x O x^{-1} = O
    xinv = scal(Fr(1, n), conj(x))
    normal = all(inO(mul(mul(x, e), xinv)) for e in basis)
    w = (sympy.multiplicity(2, n) % 2, sympy.multiplicity(3, n) % 2)
    types[key] = (c, D, best, Dorder, order_k, normal, w)
print("search box: O-coordinates in [-%d,%d]^4" % (R, R))
for key in sorted(types):
    c, D, f, Do, k, normal, w = types[key]
    print(" |trd|=%d nrd=%d: example %s, order mod Q^* = %d, disc Z[x] = %d, (Q(x) cap O) = Z[x] index %d -> disc %d, fundamental: %s, normalizes O: %s, W-image %s"
          % (key[0], key[1], c, k, D, f, Do, int(pari.coredisc(Do)) == Do, normal, {(0,0): "1", (1,0): "w2", (0,1): "w3", (1,1): "w6"}[w]))
print("types possible a priori (t^2/n in {0,1,2,3}):", sorted({(t, n) for n in (1,2,3,6) for t in range(0, 6) if Fr(t*t, n) in (0,1,2,3)}))
print("absent from O (no embedding): those not listed above")
allD = sorted({v[3] for v in types.values()})
print("CM discriminants of all elliptic points:", allD, " all fundamental:", all(int(pari.coredisc(x)) == x for x in allD),
      " prime support:", sorted({p for x in allD for p in sympy.factorint(-x)}))
print("elliptic types with nontrivial W-image and their image:", sorted({(v[4], {(1,0): "w2", (0,1): "w3", (1,1): "w6"}[v[6]]) for v in types.values() if v[6] != (0,0)}))

print("\n== R3. Euler characteristics and Riemann-Hurwitz")
chi1 = -Fr(1, 6)*(2-1)*(3-1)
print("chi(O^1/+-1 \\ H) = -(1/6)prod_{p|6}(p-1) =", chi1)
print("chi of (2,4,6) triangle orbifold = -(1-1/2-1/4-1/6) =", -(1 - Fr(1,2) - Fr(1,4) - Fr(1,6)), "; 4 * that =", 4*-(1 - Fr(1,2) - Fr(1,4) - Fr(1,6)), "(= chi1, so [Gamma^*: O^1] = 4 = |W| is consistent)")
for name, deg, es in [("X_6 -> P^1_j (deg 4, three branch points e=2)", 4, [2,2,2]),
                      ("component of Y_3 -> P^1_j (deg 72, e=4,6,2)", 72, [4,6,2]),
                      ]:
    twog2 = deg*(-2) + sum(deg - deg//e for e in es)
    print(" %s: 2g-2 = %d, g = %s" % (name, twog2, Fr(twog2 + 2, 2)))
print(" component of Y_3 = (O^1 cap K_3)\\H, torsion-free of index 18 in O^1/+-1: 2g-2 = 18*(-chi1) =", 18*(-chi1), "-> g =", (18*(-chi1)+2)/2)
print(" (X_6 genus 0 forces all three of 0, oo, -16/27 to be branch points of X_6 -> P^1_j with")
print("  pairwise distinct nontrivial inertia generators s0*s_oo*s_-16/27 = 1 generating W = (Z/2)^2)")

print("\n== R4. |Gamma'| and component stabiliser")
res = list(product(range(3), repeat=4))
O3 = [elt(c) for c in res]
def red3(x): return tuple(int(v) % 3 for v in coords_q(x))
units = [x for x in O3 if nrd(x) % 3 != 0]
norm1 = [x for x in units if nrd(x) % 3 == 1]
print("|(O/3O)^*| =", len(units), " |(O/3O)^1| (nrd = 1 mod 3) =", len(norm1), " nrd surjective onto F_3^*:", len(norm1) < len(units))
print("|Gamma'| = |W| * |(O/3O)^*| / |{+-1}| =", 4*len(units)//2)
print("pi_0(Y_3) = Zhat^*/nrd(K_3 Zhat^*)... = (Z/3)^*: 2 geometric components; stabiliser order 144/2 =", 144//2)
print("degree of a component over X_6: |(O/3O)^1/{+-1}| =", len(norm1)//2, "; over P^1_j: 4*18 =", 4*len(norm1)//2)
print("144 =", sympy.factorint(144), " -> p does not divide |Gamma_M| for p >= 5")

print("\n== R5. what counterexample F1 shows")
for p in [331, 337, 347, 349, 353]:
    tw = pari('nfdisc(x^2-%d)' % (43*p)); untw = pari('nfdisc(x^2-43)')
    print(" p=%d: fibre at j=1 of y^2=p j(27j+16): disc %s (p | disc: %s); of the untwisted y^2=j(27j+16): disc %s (p | disc: %s); residue fields over the branch points j=0,-16/27 of the twisted cover: Q (totally ramified points), unramified at p"
          % (p, tw, int(tw) % p == 0, untw, int(untw) % p == 0))
print(" In F1 the inertia groups at the two branch points are the same group Z/2, so Lemma NV step 3 allows I_V = Z/2;")
print(" NV's step 4 needs two branch points whose inertia images in an abelian quotient generate different subgroups.")

print("\n== R6. neatness: elliptic x with x^k in Q^* K_3 only if x^k central")
def in_QK3(y):
    n = nrd(y)
    v2, v3 = sympy.multiplicity(2, n.numerator) - sympy.multiplicity(2, n.denominator), sympy.multiplicity(3, n.numerator) - sympy.multiplicity(3, n.denominator)
    if v2 % 2 or v3 % 2: return False
    q = Fr(2)**(v2//2) * Fr(3)**(v3//2)
    for s in (1, -1):
        z = scal(Fr(s)/q, y)
        if not inO(z): continue
        diff = add(z, (Fr(-1), 0, 0, 0))
        if all(Fr(v) % 3 == 0 for v in coords_q(diff)): return True
    return False
bad = []
for key, (c, D, f, Do, k, normal, w) in sorted(types.items()):
    x = elt(c); y = x
    for e in range(1, k):
        if in_QK3(y) and not (y[1] == y[2] == y[3] == 0): bad.append((key, e))
        y = mul(y, x)
print(" violations:", bad, "-> ramification index of Y_3 -> P^1_j at an elliptic point = its order in B^*/Q^*")

print("\n== R7. Prop. TS tested on the W-layer X_6 -> P^1_j with real fields (30 samples)")
# Elkies' model as checked in docs/research/rv-h-cm.md §2: t = 1 + 27j/16, Q(X^6) = Q(t)(sqrt(-t), sqrt(3(t-1)))
#   = Q(j)(sqrt(-(27j+16)), sqrt(j)) up to rational squares. Constants -1, 3: p-units for p >= 5 (no vertical
#   ramification on this layer, independently of Lemma NV). Prop. TS predicts: p >= 5 ramifies in the fibre field
#   iff j0 meets 0 (e=2 on this layer) with odd v_p(j0), or -16/27 with odd v_p(j0+16/27), or oo with odd v_p(1/j0).
import random
random.seed(1111)
plist = list(sympy.primerange(5, 400))
def vpq(q, p):
    q = Fr(q); return sympy.multiplicity(p, q.numerator) - sympy.multiplicity(p, q.denominator)
allok = True
for k in range(30):
    p = random.choice(plist); kind = k % 4; m = random.randint(1, 4)
    if kind == 0:   j0 = Fr(p**m * random.randint(1, 30), random.randint(1, 30))           # meets 0
    elif kind == 1: j0 = Fr(-16, 27) + Fr(p**m * random.randint(1, 30), random.randint(1, 30))   # meets -16/27
    elif kind == 2: j0 = Fr(random.randint(1, 30), p**m)                                    # meets oo
    else:           j0 = Fr(random.randint(-500, 500), random.randint(1, 50))              # generic
    if j0 == 0 or j0 == Fr(-16, 27): j0 += 1
    a1 = j0.numerator * j0.denominator                         # sqrt(j0) ~ sqrt(num*den)
    q2 = -(27*j0 + 16); a2 = q2.numerator * q2.denominator
    pol = pari('polcompositum(x^2-(%d), x^2-(%d))[1]' % (a1, a2)) if not (sympy.sqrt(sympy.Integer(a1)).is_rational or sympy.sqrt(sympy.Integer(a2)).is_rational) else None
    if pol is None:
        a = a2 if sympy.sqrt(sympy.Integer(a1)).is_rational else a1
        pol = pari('x^2-(%d)' % a) if not sympy.sqrt(sympy.Integer(a)).is_rational else pari('x')
    disc = pari.nfdisc(pol) if pari.poldegree(pol) > 1 else 1
    ram = int(disc) % p == 0
    v0, v2 = vpq(j0, p), vpq(j0 + Fr(16, 27), p)
    pred = (v0 > 0 and v0 % 2 == 1) or (v0 < 0 and (-v0) % 2 == 1) or (v2 > 0 and v2 % 2 == 1)
    ok = ram == pred; allok = allok and ok
    print(" p=%d j0=%s v_p(j0)=%d v_p(j0+16/27)=%d: p ramified in fibre: %s, Prop. TS predicts: %s %s" % (p, j0, v0, v2, ram, pred, "ok" if ok else "MISMATCH"))
print(" all 30 agree:", allok)
