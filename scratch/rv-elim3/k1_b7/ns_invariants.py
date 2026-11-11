"""Galois-invariant part of NS(X_{beta,theta}) (data from ns_lattice.py).
Cases: theta generic (Gal(K/Q) = <s_b, s_i, s_t>), and theta in {1, -1, beta, -beta} classes,
where s_t is identified with a product of the other generators.
Prints rank, Gram, discriminant, gcd of norms, and whether -2 / 0 are represented (short search).
"""
import json, itertools
from sympy import Matrix, Rational, sympify, ilcm, gcd
from sympy.matrices.normalforms import hermite_normal_form
D = json.load(open('scratch/rv-elim3/k1_b7/ns_data.json'))
GB = Matrix(D['GB'])
Lb = Matrix([[sympify(x) for x in r] for r in D['Lb']])
gal = {g: Matrix([[sympify(x) for x in r] for r in D['gal'][g]]) for g in 'bit'}
# work in L-coordinates: x_L row vector, curve-coords = x_L * Lb
Lbi = Lb.inv()
galL = {g: (Lb * gal[g].T * Lbi) for g in 'bit'}  # acts on row vectors: x -> x * galL? check below
GL = Lb * GB * Lb.T
for g in 'bit':
    assert galL[g] * GL * galL[g].T == GL
    assert all(x.is_integer for x in galL[g])

def invariant_lattice(gens):
    A = Matrix.vstack(*[(galL[g] - Matrix.eye(20)).T for g in gens])
    ns = A.nullspace()   # column vectors x with (M-1)^T x = 0  <=> x*M = x
    if not ns:
        return None
    B = Matrix.hstack(*ns).T
    den = ilcm(*[x.q for x in B])
    B = (B * den).applyfunc(int)
    # saturate in Z^20: lattice = Q-span ∩ Z^20
    # use HNF of kernel of the complementary: simpler: Smith-like via LLL-free method
    from sympy import Matrix as M
    # Z-basis of (Q B) ∩ Z^20 = kernel over Z of an integer matrix C whose rows span B^perp
    Cperp = B.nullspace()  # vectors y with B y = 0
    C = Matrix.hstack(*Cperp).T
    denc = ilcm(*[x.q for x in C]); C = (C*denc).applyfunc(int)
    # integer kernel of C
    from sympy.matrices.normalforms import smith_normal_form
    K = int_kernel(C)
    return K

def int_kernel(C):
    # integer kernel via column-style HNF on [C^T | I]
    m, k = C.shape
    Aug = Matrix.hstack(C.T, Matrix.eye(k))
    H = hermite_normal_form(Aug.T).T  # not reliable for kernel; do manual
    return manual_kernel(C)

def manual_kernel(C):
    # Gaussian elimination over Z with unimodular column ops (extended gcd)
    C = [list(map(int, r)) for r in C.tolist()]
    m = len(C); k = len(C[0])
    U = [[int(i == j) for j in range(k)] for i in range(k)]  # columns transform
    col = 0
    for r in range(m):
        # make C[r][col:] have single nonzero at col
        while True:
            nz = [j for j in range(col, k) if C[r][j] != 0]
            if not nz:
                break
            p = min(nz, key=lambda j: abs(C[r][j]))
            # swap p and col
            for M_ in (C, ):
                for row in M_: row[p], row[col] = row[col], row[p]
            for row in U: row[p], row[col] = row[col], row[p]
            done = True
            for j in range(col+1, k):
                if C[r][j]:
                    q = C[r][j] // C[r][col]
                    for row in C: row[j] -= q * row[col]
                    for row in U: row[j] -= q * row[col]
                    if C[r][j]: done = False
            if done:
                break
        if any(C[r][j] for j in range(col, k)):
            col += 1
    return Matrix([[U[i][j] for i in range(k)] for j in range(col, k)])

def analyse(name, gens):
    K = invariant_lattice(gens)
    G = K * GL * K.T
    print(f'--- {name}: rank {G.rows}, disc {G.det()}')
    print('    norms mod 4 of basis and pairings:', sorted(set(int(G[i,i]) % 4 for i in range(G.rows))),
          'gcd of off-diagonal', gcd([int(G[i,j]) for i in range(G.rows) for j in range(G.rows) if i!=j] + [0]))
    # is x^2 ≡ 0 mod 4 for all x?  <=> diag ≡ 0 mod 4 and off-diag even
    all4 = all(int(G[i,i]) % 4 == 0 for i in range(G.rows)) and all(int(G[i,j]) % 2 == 0 for i in range(G.rows) for j in range(G.rows))
    print('    every class has D^2 ≡ 0 (mod 4):', all4)
    return K, G

res = {}
res['generic'] = analyse('theta generic (K = Q(i,sqrt b,sqrt t), Gal = (Z/2)^3)', 'bit')
# theta = 1: sqrt(theta) rational, s_t absent
res['t=1'] = analyse('theta = 1', 'bi')
# theta = -1: sqrt(theta) = i: s_i also flips sqrt(theta)
galL['I'] = galL['i'] * galL['t']; galL['B'] = galL['b'] * galL['t']
res['t=-1'] = analyse('theta = -1', 'Ib')
res['t=b'] = analyse('theta = beta', 'iB')
json.dump({k: {'K': [[int(x) for x in v[0].row(i)] for i in range(v[0].rows)],
               'G': [[int(x) for x in v[1].row(i)] for i in range(v[1].rows)]} for k, v in res.items()},
          open('scratch/rv-elim3/k1_b7/ns_inv.json', 'w'))
G = res['generic'][1]
print('generic Gram:'); print(G)
