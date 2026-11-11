"""A9 check: for B=(-1,3)_Q (discriminant 6), H_1 = B (left B-action), complex structure
= right multiplication by J in B(x)R with J^2=-1.  Compute the Q-dimension of the commutant of
R_J inside End_Q(B)=M_4(Q) for three J's, and check End_Q(B) = L(B)R(B) (i.e. B(x)B^op).
Expected: generic J -> dim 4 (=B); J in R[w] with w^2=-1 or w^2=-3 rational -> dim 8 (=M_2(k)),
and the commutant then contains a nonzero nilpotent (so it is M_2(k), not a division algebra)."""
import sympy as sp
import cypari2
pari = cypari2.Pari()

a, b = -1, 3
# Hilbert symbols: B ramified exactly at {2,3}
ram = [p for p in [2, 3, 5, 7, 11, 13] if pari.hilbert(a, b, p) == -1]
print("ramified finite primes (p<=13):", ram, " infinite:", "split" if (a > 0 or b > 0) else "ram")

# basis 1,i,j,k with i^2=a, j^2=b, k=ij, k^2=-ab
def mul(x, y):
    x0, x1, x2, x3 = x; y0, y1, y2, y3 = y
    return (x0*y0 + a*x1*y1 + b*x2*y2 - a*b*x3*y3,
            x0*y1 + x1*y0 - b*x2*y3 + b*x3*y2,
            x0*y2 + x2*y0 + a*x1*y3 - a*x3*y1,
            x0*y3 + x3*y0 + x1*y2 - x2*y1)
E = [tuple(1 if t == s else 0 for t in range(4)) for s in range(4)]
# sanity: associativity on basis
for u in E:
    for v in E:
        for w in E:
            assert tuple(sp.expand(t) for t in mul(mul(u, v), w)) == tuple(sp.expand(t) for t in mul(u, mul(v, w)))
def Lm(x): return sp.Matrix(4, 4, lambda r, c: mul(x, E[c])[r])
def Rm(x): return sp.Matrix(4, 4, lambda r, c: mul(E[c], x)[r])
prods = [ (Lm(u)*Rm(v)).reshape(16, 1) for u in E for v in E]
print("rank of L(B)R(B) in M_4(Q):", sp.Matrix.hstack(*prods).rank())

def commutant_dim(J, basis_field):
    """rational X in M_4(Q) with X R_J = R_J X; split coefficients over a Q-basis of the field."""
    X = sp.Matrix(4, 4, sp.symbols('x0:16'))
    RJ = Rm(J)
    eqs = []
    for e in (X*RJ - RJ*X):
        e = sp.expand(e)
        # e is Q-linear in x's with coefficients in Q(basis_field); separate components
        coeffs = sp.Poly(e, *basis_field).as_dict() if basis_field else {(): e}
        eqs += list(coeffs.values())
    A, _ = sp.linear_eq_to_matrix(eqs, list(X))
    ns = A.nullspace()
    return len(ns), [sp.Matrix(4, 4, list(v)) for v in ns]

s2, s10, s3 = sp.symbols('s2 s10 s3')  # stand for sqrt2, sqrt10, sqrt3 (independent over Q)
cases = {
  "generic J=sqrt10 i + j + sqrt2 k": ((0, s10, 1, s2), {s10**2: 10, s2**2: 2}, (s2, s10)),
  "J=2i+j (J^2=-1, rational)": ((0, 2, 1, 0), {}, ()),
  "J=(3i+j+k)/sqrt3 (k=Q(sqrt-3))": ((0, 3/s3, 1/s3, 1/s3), {s3**2: 3}, (s3,)),
}
for name, (J, rel, gens) in cases.items():
    # check J^2 = -1 using the relations
    sq = [sp.simplify(sp.expand(t).subs(rel)) for t in mul(J, J)]
    sq = [sp.nsimplify(sp.expand(t).subs({s10: sp.sqrt(10), s2: sp.sqrt(2), s3: sp.sqrt(3)})) for t in mul(J, J)]
    # multiply J by s3 to keep polynomial form for the third case
    Jp = J
    if name.startswith("J=(3i"):
        Jp = (0, 3, 1, 1)   # commutant of R_J = commutant of R_{sqrt3 J}
    d, basis = commutant_dim(Jp, gens)
    nil = False
    if d == 8:
        # look for a nonzero nilpotent: sum of basis elements with small integer coefficients
        import itertools
        for cs in itertools.product([-1, 0, 1], repeat=8):
            if any(cs):
                M = sum((c*bm for c, bm in zip(cs, basis)), sp.zeros(4, 4))
                if M != sp.zeros(4, 4) and (M*M) == sp.zeros(4, 4):
                    nil = True; break
    print(f"{name}: J^2 = {sq}; dim_Q commutant = {d}; nonzero nilpotent found: {nil}")
