"""Exact check that the principally polarized abelian surface A = C^2/(Omega Z^2 + Z^2), Omega = z[[3,5],[5,10]],
z = (-4+sqrt(-24))/10 (root of 5z^2+4z+2), is a point of the discriminant-six QM locus with CM by the maximal order of
Q(sqrt(-6)) (the point P_-24), for the QM datum of N5 L410-420 / h-trust A1:
  O = Z<1, I, (1+J)/2, (I+IJ)/2>, I^2=2, J^2=-3, IJ=-JI, mu = 2J+IJ, Rosati(a) = mu^{-1} conj(a) mu.
End(A) = {R in M4(Z): alpha*Pi = Pi*R for some alpha}, Pi = (Omega | I2), solved exactly over Z (PARI matkerint).
Then: search I, J in End(A) with the relations, O in End(A), Rosati condition for E = [[0,I],[-I,0]];
then the commutant of O in End(A) and its discriminant.  Pure Python + sympy + cypari2.  Arg: coefficient bound."""
import itertools, sys
from sympy import Matrix, symbols, Rational, eye
import cypari2
pari = cypari2.Pari()
def mm(a, b): return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(4)) for j in range(4)) for i in range(4))
def add(a, b, s=1): return tuple(tuple(a[i][j] + s*b[i][j] for j in range(4)) for i in range(4))
def sc(c, a): return tuple(tuple(c*a[i][j] for j in range(4)) for i in range(4))
def tr(a): return sum(a[i][i] for i in range(4))
def T(a): return tuple(tuple(a[j][i] for j in range(4)) for i in range(4))
ID = tuple(tuple(int(i == j) for j in range(4)) for i in range(4))
ZERO = sc(0, ID)
Mq = Matrix([[3, 5], [5, 10]])
v = symbols('r0:16')
R11 = Matrix(2, 2, v[0:4]); R12 = Matrix(2, 2, v[4:8]); R21 = Matrix(2, 2, v[8:12]); R22 = Matrix(2, 2, v[12:16])
# z root of a z^2 + b z + c (default [5,4,2], disc -24; argv[2:5] may give another form with 5 | a)
fa, fb, fc = (int(x) for x in sys.argv[2:5]) if len(sys.argv) > 4 else (5, 4, 2)
print("form", (fa, fb, fc), "disc", fb*fb - 4*fa*fc)
# alpha = Omega R12 + R22 and alpha Omega = Omega R11 + R21, Omega = z Mq, with z^2 = -(fb z + fc)/fa:
eqs = list(-fb*Mq*R12*Mq + fa*R22*Mq - fa*Mq*R11) + list(-fc*Mq*R12*Mq - fa*R21)
A = [[int(e.coeff(x)) for x in v] for e in eqs]
K = pari.matkerint(pari.matrix(len(A), 16, [a for row in A for a in row]))
def tomat(col):
    c = [int(x) for x in col]
    return ((c[0], c[1], c[4], c[5]), (c[2], c[3], c[6], c[7]), (c[8], c[9], c[12], c[13]), (c[10], c[11], c[14], c[15]))
basis = [tomat([K[r, c] for r in range(16)]) for c in range(int(pari.matsize(K)[1]))]
print("rank End(A) =", len(basis))
Bm = pari.matrix(16, len(basis), [basis[c][i][j] for i in range(4) for j in range(4) for c in range(len(basis))])
def incoords(R):
    """True iff R is an integral combination of the basis."""
    vec = pari.matrix(16, 1, [R[i][j] for i in range(4) for j in range(4)])
    try:
        s = pari.matinverseimage(Bm, vec)
    except cypari2.PariError:
        return False
    if int(pari.matsize(s)[0]) == 0:
        return False
    return all(int(pari.denominator(s[i, 0])) == 1 for i in range(len(basis)))
print("End(A) closed under products:", all(incoords(mm(a, b)) for a in basis for b in basis))
E = ((0, 0, 1, 0), (0, 0, 0, 1), (-1, 0, 0, 0), (0, -1, 0, 0))
Einv = sc(-1, E)
def ros(R): return mm(mm(Einv, T(R)), E)      # R^T E = E R'
print("End(A) Rosati-stable:", all(incoords(ros(b)) for b in basis))
bound = int(sys.argv[1]) if len(sys.argv) > 1 else 2
Is, Js = [], []
for cs in itertools.product(range(-bound, bound + 1), repeat=len(basis)):
    R = ZERO
    for c, b in zip(cs, basis):
        if c: R = add(R, sc(c, b))
    if tr(R) != 0: continue
    S = mm(R, R)
    if S == sc(2, ID): Is.append(R)
    elif S == sc(-3, ID): Js.append(R)
print(f"bound {bound}: #(R^2=2) = {len(Is)}, #(R^2=-3) = {len(Js)}")
found = None
# Stage 1: an embedding iota of O (I^2=2, J^2=-3, IJ=-JI, (1+J)/2 and (I+IJ)/2 integral) with Rosati-stable image.
def flat(R): return [R[i][j] for i in range(4) for j in range(4)]
emb = None
for Ii in Is:
    for Jj in Js:
        IJ = mm(Ii, Jj)
        if IJ != sc(-1, mm(Jj, Ii)): continue
        if any(x % 2 for row in add(ID, Jj) for x in row) or any(y % 2 for row in add(Ii, IJ) for y in row): continue
        emb = (Ii, Jj); break
    if emb: break
print("embedding of O into End(A) found:", emb is not None)
Ii, Jj = emb; IJ = mm(Ii, Jj)
Ob = [ID, Ii, sc(Rational(1, 2), add(ID, Jj)), sc(Rational(1, 2), add(Ii, IJ))]   # Z-basis of iota(O)
Bq = [ID, Ii, Jj, IJ]
Mb = Matrix([flat(b) for b in Bq]).T
print("iota(O) Rosati-stable:", all(Mb.rank() == Mb.row_join(Matrix(flat(ros(a)))).rank() for a in (Ii, Jj)))
# Stage 2: nu with Rosati(x) = nu^{-1} conj(x) nu on iota(B): nu*ros(a) + a*nu = 0 for a = I, J.
xs = symbols('x0:4')
nuS = Matrix(4, 4, lambda i, j: sum(xs[k]*Bq[k][i][j] for k in range(4)))
eqs = []
for a in (Ii, Jj):
    eqs += list(nuS*Matrix(ros(a)) + Matrix(a)*nuS)
from sympy import linsolve
sol = list(linsolve(eqs, xs))[0]
free = [s for s in sol if s.free_symbols]
nu = Matrix(4, 4, lambda i, j: sum(sol[k]*Bq[k][i][j] for k in range(4)))
fs = list(set().union(*[s.free_symbols for s in sol]))
assert len(fs) == 1
nu = nu.subs(fs[0], 1)
nu2 = nu*nu
print("nu (in I,J,IJ coords) =", [s.subs(fs[0], 1) for s in sol], "; nu^2 =", nu2[0, 0], "* Id:", nu2 == nu2[0, 0]*eye(4))
# scale nu to mu' with mu'^2 = -6 and check mu' in iota(O)
from sympy import sqrt as ssqrt
lam = ssqrt(Rational(-6, 1)/nu2[0, 0])
mup = nu*lam
MO = Matrix([flat(b) for b in Ob]).T
cO = MO.solve(Matrix(list(mup.T)).reshape(16, 1)) if False else MO.gauss_jordan_solve(Matrix([mup[i, j] for i in range(4) for j in range(4)]))[0]
print("mu' = lam*nu, lam =", lam, "; mu' in iota(O) with O-coords", list(cO.T), ":", all(c.is_integer for c in cO))
# Stage 3: gamma in iota(O), normalizing iota(O), with gamma mu' gamma^{-1} = +-mu, mu = 2J+IJ.
mu4 = 2*Matrix(Jj) + Matrix(IJ)
def inO(X):
    c = MO.gauss_jordan_solve(Matrix([X[i, j] for i in range(4) for j in range(4)]))[0]
    return all(ci.is_integer for ci in c)
gam = None
for cs in itertools.product(range(-3, 4), repeat=4):
    if not any(cs): continue
    G = sum((c*Matrix(b) for c, b in zip(cs, Ob)), Matrix.zeros(4, 4))
    if G.det() == 0: continue
    for sgn in (1, -1):
        if G*mup == sgn*mu4*G:
            Gi = G.inv()
            if all(inO(G*Matrix(b)*Gi) for b in Ob) and all(inO(Gi*Matrix(b)*G) for b in Ob):
                gam = G; break
    if gam is not None: break
print("normalizer element gamma with gamma mu' gamma^-1 = +-mu found:", gam is not None)
Gi = gam.inv()
I2 = Gi*Matrix(Ii)*gam; J2 = Gi*Matrix(Jj)*gam
def tup(X): return tuple(tuple(int(X[i, j]) for j in range(4)) for i in range(4))
assert all(x.is_integer for x in list(I2) + list(J2))
Ii, Jj = tup(I2), tup(J2)
IJ = mm(Ii, Jj); mu = add(sc(2, Jj), IJ)
ok = (mm(Ii, Ii) == sc(2, ID) and mm(Jj, Jj) == sc(-3, ID) and IJ == sc(-1, mm(Jj, Ii))
      and incoords(Ii) and incoords(Jj)
      and not any(x % 2 for row in add(ID, Jj) for x in row) and not any(y % 2 for row in add(Ii, IJ) for y in row)
      and all(incoords(tuple(tuple(x//2 for x in row) for row in g)) for g in (add(ID, Jj), add(Ii, IJ)))
      and all(sc(6, ros(a)) == mm(mm(mu, a), mu) for a in (Ii, Jj)))
if ok: found = (Ii, Jj, mu)
print("O-embedding with Rosati a -> mu^{-1} conj(a) mu found:", found is not None)
if found:
    Ii, Jj, mu = found
    print("I =", [list(r) for r in Ii]); print("J =", [list(r) for r in Jj])
    print("mu^2 = -6:", mm(mu, mu) == sc(-6, ID))
    O_gens = [ID, Ii, sc(Rational(1, 2), add(ID, Jj)), sc(Rational(1, 2), add(Ii, mm(Ii, Jj)))]
    print("O generators lie in End(A):", all(incoords(tuple(tuple(int(x) for x in r) for r in g)) for g in O_gens))
    rows = []
    for g in (Ii, Jj):
        for r in range(4):
            for s in range(4):
                rows.append([add(mm(b, g), mm(g, b), -1)[r][s] for b in basis])
    Kc = pari.matkerint(pari.matrix(len(rows), len(basis), [x for row in rows for x in row]))
    comm = []
    for c in range(int(pari.matsize(Kc)[1])):
        R = ZERO
        for k in range(len(basis)): R = add(R, sc(int(Kc[k, c]), basis[k]))
        comm.append(R)
    print("rank of commutant of O in End(A) =", len(comm))
    # each commutant element acts K-linearly on Q^4 = K^2, so tr4 = 2 Tr_{K/Q}; disc = det(Tr(x_a x_b))
    G = Matrix(len(comm), len(comm), lambda a, b: Rational(tr(mm(comm[a], comm[b])), 2))
    print("discriminant of the commutant order det(Tr_{K/Q}(x_a x_b)) =", G.det())
    for c in comm:
        t = Rational(tr(c), 4)
        N2 = Matrix(c)*Matrix(c) - 2*t*Matrix(c)
        print("  basis element: Tr_{K/Q} =", 2*t, "; Norm =", -N2[0, 0] if N2 == N2[0, 0]*eye(4) else "non-scalar")
