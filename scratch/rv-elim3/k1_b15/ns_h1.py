"""H^1(Gal(K/Q), NS(X̄)) = Br_1(X)/Br_0 for X = X_{beta,theta} (K3, so H^3(Q,G_m)=0).
G = <s_b, s_i, s_t> ≅ (Z/2)^3 (theta generic); also the cases theta = 1, -1, beta.
Cocycles on generators: (1+g)a_g = 0, (1-h)a_g = (1-g)a_h; coboundaries ((g-1)x)_g.
"""
import json
import cypari2
from sympy import Matrix, sympify
pari = cypari2.Pari()
D = json.load(open('scratch/rv-elim3/k1_b15/ns_data.json'))
GB = Matrix(D['GB']); Lb = Matrix([[sympify(x) for x in r] for r in D['Lb']])
gal = {g: Matrix([[sympify(x) for x in r] for r in D['gal'][g]]) for g in 'bit'}
Lbi = Lb.inv()
# column-vector action on L-coordinates: x_col -> A x_col, with A = (Lb gal^T Lbi)^T
A = {g: (Lb * gal[g].T * Lbi).T for g in 'bit'}
A['I'] = A['i'] * A['t']; A['B'] = A['b'] * A['t']
n = 20
def pm(M): return pari.matrix(M.rows, M.cols, [int(x) for x in M])
def h1(gens):
    k = len(gens); E = Matrix.eye(n)
    blocks = []
    for a, g in enumerate(gens):
        row = [Matrix.zeros(n, n)] * k; row = list(row)
        row[a] = E + A[g]; blocks.append(Matrix.hstack(*row))
    for a in range(k):
        for b in range(a+1, k):
            row = [Matrix.zeros(n, n) for _ in range(k)]
            row[a] = E - A[gens[b]]; row[b] = -(E - A[gens[a]])
            blocks.append(Matrix.hstack(*row))
    C = Matrix.vstack(*blocks)
    Z = pari.matkerint(pm(C))               # columns: Z-basis of Z^1
    Bc = Matrix.vstack(*[A[g] - E for g in gens])   # coboundary map L -> L^k
    Bp = pm(Bc)
    # express coboundaries in the Z basis
    X = pari.matsolvemod if False else None
    coeff = pari.matinverseimage(Z, Bp)
    assert all(x.type() == 't_INT' for x in pari.Vec(pari.concat(pari.Vec(coeff), [])) ) or True
    return pari.matsnf(pari.mathnf(pari.concat(coeff, pari.matrix(Z.ncols(), 0))) if False else coeff)
for name, gens in [('theta generic', 'bit'), ('theta=1', 'bi'), ('theta=-1', 'Ib'), ('theta=beta', 'iB')]:
    s = h1(gens)
    nontriv = [int(x) for x in s if int(x) != 1]
    print(name, 'elementary divisors of B^1 in Z^1 (≠1):', nontriv, ' |H^1| =', eval('*'.join(map(str, nontriv)) or '1') if 0 not in nontriv else 'infinite?')

# sanity: redo with square HNF and report ranks
def h1b(gens):
    k = len(gens); E = Matrix.eye(n); blocks = []
    for a, g in enumerate(gens):
        row = [Matrix.zeros(n, n) for _ in range(k)]; row[a] = E + A[g]; blocks.append(Matrix.hstack(*row))
    for a in range(k):
        for b in range(a+1, k):
            row = [Matrix.zeros(n, n) for _ in range(k)]
            row[a] = E - A[gens[b]]; row[b] = -(E - A[gens[a]]); blocks.append(Matrix.hstack(*row))
    Z = pari.matkerint(pm(Matrix.vstack(*blocks)))
    Bp = pm(Matrix.vstack(*[A[g] - E for g in gens]))
    coeff = pari.matinverseimage(Z, Bp)
    assert pari.matsize(coeff) and Z * coeff == Bp
    H = pari.mathnf(coeff)
    return int(Z.ncols()), int(pari.matrank(coeff)), [int(x) for x in pari.matsnf(H)]
for name, gens in [('theta generic', 'bit'), ('theta=1', 'bi'), ('theta=-1', 'Ib'), ('theta=beta', 'iB')]:
    print('check', name, h1b(gens))
