# Independent recomputation (PARI matkerint/qflllgram) of NS(Xbar)^G from el-k3's ns_data.json
# (rerun copy for a given beta), including the case theta = -beta that el-k3 omits.
import json, sys, cypari2
from sympy import Matrix, sympify
pari = cypari2.Pari()
D = json.load(open(sys.argv[1]))
GB = Matrix(D['GB']); Lb = Matrix([[sympify(x) for x in r] for r in D['Lb']])
gal = {g: Matrix([[sympify(x) for x in r] for r in D['gal'][g]]) for g in 'bit'}
Lbi = Lb.inv()
A = {g: (Lb * gal[g].T * Lbi).T for g in 'bit'}      # column action on L-coordinates
GL = Lb * GB * Lb.T
pm = lambda M: pari.matrix(M.rows, M.cols, [int(x) for x in M])
E = Matrix.eye(20)
cases = {'generic': ['b', 'i', 't'], 'theta=1': ['b', 'i'], 'theta=-1': ['b', 'it'],
         'theta=beta': ['bt', 'i'], 'theta=-beta': ['bt', 'it']}
def mat(word):
    M = E
    for ch in word: M = M * A[ch]
    return M
for name, gens in cases.items():
    C = Matrix.vstack(*[mat(g) - E for g in gens])
    K = pari.matkerint(pm(C))                       # columns: Z-basis of invariants (saturated)
    G = pari.mattranspose(K) * pm(GL) * K
    n = int(pari.matsize(G)[0])
    ev = all(int(G[i, i]) % 4 == 0 for i in range(n)) and all(int(G[i, j]) % 2 == 0 for i in range(n) for j in range(n))
    sig = pari.qfsign(G)
    # does the lattice represent -2 or an odd pairing? min |D.D'| over basis pairs; also qfminim on -G restricted? (indefinite: skip)
    print(f"{name}: rank {n}, disc {pari.matdet(G)}, signature {sig}, all D^2 = 0 mod 4 and D.D' even: {ev}")
