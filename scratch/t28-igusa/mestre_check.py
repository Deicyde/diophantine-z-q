"""t28-igusa: computer-algebra checks for the Mestre ("Gram") route to the (<=) direction of T28.
Run from the repo root: ~/pyenv/bin/python -I scratch/t28-igusa/mestre_check.py
Checks (exact arithmetic, sympy; PARI only for genus2igusa):
 (1) Clebsch covariants i=(f,f)_4, Delta=(i,i)_2, y1=(f,i)_4, y2=(i,y1)_2, y3=(i,y2)_2 and the
     Clebsch invariants A=(f,f)_6, B=(i,i)_4, C=(i,Delta)_4, D=(y3,y1)_2.
 (2) The Gram matrix G_ij=(y_i,y_j)_2 and the coefficients a_ijk=(f,y_i y_j y_k)_6.
 (3) The reconstruction identity  kappa * det(G)^3 * f = sum a_ijk (adj G y)_i (adj G y)_j (adj G y)_k
     and the conic identity  sum adj(G)_ij y_i y_j = 0, on random integer sextics.
 (4) Invariance: G_ij, a_ijk, A..D under f -> f|M scale by det(M)^w (random M).
 (5) Igusa's J2,J4,J6,J10 (PARI genus2igusa normalization, the polynomials of the leaf) as
     polynomials in A,B,C,D: solved by interpolation and checked on fresh samples.
"""
import random, itertools, sympy as sp, cypari2
pari = cypari2.Pari()
x, z = sp.symbols('x z')
random.seed(20261112)

def tv(phi, psi, k):
    m = sp.Poly(phi, x, z).total_degree() if phi != 0 else 0
    n = sp.Poly(psi, x, z).total_degree() if psi != 0 else 0
    s = 0
    for j in range(k + 1):
        s += (-1)**j * sp.binomial(k, j) * sp.diff(phi, x, k - j, z, j) * sp.diff(psi, x, j, z, k - j)
    return sp.expand(sp.factorial(m - k) * sp.factorial(n - k) / (sp.factorial(m) * sp.factorial(n)) * s)

def binform(c):  # c[i] = coefficient of x^i, homogenized to degree len(c)-1
    d = len(c) - 1
    return sp.expand(sum(ci * x**i * z**(d - i) for i, ci in enumerate(c)))

def covs(f):
    i = tv(f, f, 4); De = tv(i, i, 2)
    y1 = tv(f, i, 4); y2 = tv(i, y1, 2); y3 = tv(i, y2, 2)
    A = tv(f, f, 6); B = tv(i, i, 4); C = tv(i, De, 4); D = tv(y3, y1, 2)
    return dict(i=i, De=De, y=[y1, y2, y3], A=A, B=B, C=C, D=D)

def gram(f, cv):
    y = cv['y']
    G = sp.Matrix(3, 3, lambda r, s: tv(y[r], y[s], 2))
    a = {}
    for t in itertools.combinations_with_replacement(range(3), 3):
        a[t] = tv(f, sp.expand(y[t[0]] * y[t[1]] * y[t[2]]), 6)
    return G, a

def act(f, M, deg=6):
    (p, q), (r, s) = M
    return sp.expand(f.subs({x: p * x + q * z, z: r * x + s * z}, simultaneous=True))

def igusa(c):
    fx = sum(ci * sp.Symbol('t')**i for i, ci in enumerate(c))
    v = pari("genus2igusa(" + sp.sstr(fx).replace("**", "^").replace("t", "x") + ")")
    return [sp.Rational(str(u)) for u in v]

def rand_sextic():
    while True:
        c = [random.randint(-6, 6) for _ in range(7)]
        if c[6] != 0 and sp.discriminant(sum(ci * x**i for i, ci in enumerate(c)), x) != 0:
            return c

# (3) reconstruction identity
kappas = set()
for trial in range(8):
    c = rand_sextic(); f = binform(c); cv = covs(f); G, a = gram(f, cv)
    adj = G.adjugate(); y = cv['y']
    Y = [sp.expand(sum(adj[r, s] * y[s] for s in range(3))) for r in range(3)]
    conic = sp.expand(sum(adj[r, s] * y[r] * y[s] for r in range(3) for s in range(3)))
    assert conic == 0, "conic identity fails"
    cub = 0
    for t in itertools.product(range(3), repeat=3):
        cub += a[tuple(sorted(t))] * Y[t[0]] * Y[t[1]] * Y[t[2]]
    cub = sp.expand(cub)
    if G.det() == 0:
        print("singular Gram on sample", c); continue
    ratio = sp.simplify(cub / (G.det()**3 * f))
    assert ratio.free_symbols == set(), ("cubic not proportional to f", ratio)
    kappas.add(ratio)
print("(3) conic identity adj(G)(y,y)=0 and cubic identity sum a_ijk (adj G y)^3 = kappa det(G)^3 f: OK on 8 samples; kappa =", kappas)

# (4) invariance (weights)
c = rand_sextic(); f = binform(c); cv = covs(f); G, a = gram(f, cv)
M = ((2, -1), (3, 1)); dt = 2 * 1 - (-1) * 3
fM = act(f, M); cvM = covs(fM); GM, aM = gram(fM, cvM)
wts = {}
for k in ('A', 'B', 'C', 'D'):
    q = sp.nsimplify(cvM[k] / cv[k]); wts[k] = sp.log(q, dt).simplify() if q != 1 else 0
for r in range(3):
    for s in range(3):
        q = sp.nsimplify(GM[r, s] / G[r, s]) if G[r, s] != 0 else None
        assert q is not None and sp.log(q, dt).is_integer, (r, s, q)
for t in a:
    q = sp.nsimplify(aM[t] / a[t]); assert sp.log(q, dt).is_integer, (t, q)
print("(4) A,B,C,D, G_ij, a_ijk scale by powers of det(M) under f -> f(Mx): OK (weights of A..D:", wts, ")")

# (5) Igusa J's (leaf normalization) in terms of Clebsch A,B,C,D
Asym, Bsym, Csym, Dsym = sp.symbols('A B C D')
def wmons(w):  # monomials A^p B^q C^r D^s with 2p+4q+6r+10s = w (degrees in coefficients)
    out = []
    for p in range(w // 2 + 1):
        for q in range(w // 4 + 1):
            for r in range(w // 6 + 1):
                for s in range(w // 10 + 1):
                    if 2 * p + 4 * q + 6 * r + 10 * s == w: out.append((p, q, r, s))
    return out
samples = []
for _ in range(40):
    c = rand_sextic(); cv = covs(binform(c)); samples.append((c, [cv['A'], cv['B'], cv['C'], cv['D']], igusa(c)))
res = {}
for w, idx in ((2, 0), (4, 1), (6, 2), (10, 4)):
    B_ = wmons(w)
    rows = [[sp.prod([v**e for v, e in zip(s[1], m)]) for m in B_] for s in samples[:30]]
    rhs = [s[2][idx] for s in samples[:30]]
    Mx = sp.Matrix(rows); sol = (Mx.T * Mx).LUsolve(Mx.T * sp.Matrix(rhs))
    assert Mx * sol == sp.Matrix(rhs)
    P = sum(cf * Asym**m[0] * Bsym**m[1] * Csym**m[2] * Dsym**m[3] for cf, m in zip(sol, B_))
    for s in samples[30:]:
        assert P.subs({Asym: s[1][0], Bsym: s[1][1], Csym: s[1][2], Dsym: s[1][3]}) == s[2][idx]
    res[w] = sp.expand(P)
    print(f"(5) J{w} =", res[w])
print("(5) checked on 10 fresh samples")
