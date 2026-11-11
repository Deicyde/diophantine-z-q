"""NS lattice of X_{beta,theta}: w^2 = theta f(s) f(t), f = beta^2 s^4 - 1, with Galois action.

Curves: 16 nodes N_ab, 8 tropes T_a, T'_b, 16 graph components G_(fam,lam,eps).
Intersection numbers: nodes/tropes by the standard Kummer configuration; graph components
by solving phi(s) = psi(s) numerically (beta = 7, sqrt(theta) = 1 factored out) and matching w.
Outputs: rank, discriminant of the span, Galois-invariant sublattice for theta generic
(sigma_theta acts), its Gram matrix, and a search for small-norm vectors.
Run: ~/pyenv/bin/python scratch/el-k3/ns_lattice.py
"""
import itertools, cmath
from sympy import Matrix, Rational, zeros, eye, gcd, ilcm
import sympy

BETA = -7.0
I = 1j
LAMS = [1, I, -1, -I]
rb = cmath.sqrt(BETA)
ROOTS = [1/rb, -1/rb, I/rb, -I/rb]


def F(s0, s1):
    return BETA**2 * s0**4 - s1**4


def mat(fam, lam):
    # t-vector = M (s0, s1)
    return [[lam, 0], [0, 1]] if fam == 0 else [[0, lam], [BETA, 0]]


def sqrtk(fam):
    return 1 if fam == 0 else I * BETA   # sqrt(theta*k)/sqrt(theta)


def tvec(fam, lam, s):
    M = mat(fam, lam)
    return (M[0][0]*s[0] + M[0][1]*s[1], M[1][0]*s[0] + M[1][1]*s[1])


def wval(fam, lam, eps, s):
    return eps * sqrtk(fam) * F(*s)


def close(a, b, tol=1e-7):
    return abs(a - b) < tol * (1 + abs(a) + abs(b))


def root_index(z):
    for i, r in enumerate(ROOTS):
        if close(z, r):
            return i
    return None


def phi_on_root(fam, lam, a):
    t0, t1 = tvec(fam, lam, (ROOTS[a], 1))
    return root_index(t0 / t1)


graphs = [(fam, k, eps) for fam in (0, 1) for k in range(4) for eps in (1, -1)]
nodes = [(a, b) for a in range(4) for b in range(4)]
curves = [('N', x) for x in nodes] + [('T', a) for a in range(4)] + [('U', b) for b in range(4)] \
    + [('G', g) for g in graphs]
n = len(curves)


def gg(g1, g2):
    (f1, k1, e1), (f2, k2, e2) = g1, g2
    if (f1, k1) == (f2, k2):
        return -2 if e1 == e2 else 0
    M1, M2 = mat(f1, LAMS[k1]), mat(f2, LAMS[k2])
    # solve det[M1 s, M2 s] = 0, homogeneous quadratic in (s0, s1)
    # coefficients of s0^2, s0 s1, s1^2
    def d(s):
        a = tvec(f1, LAMS[k1], s); b = tvec(f2, LAMS[k2], s)
        return a[0]*b[1] - a[1]*b[0]
    c2 = d((1, 0)); c0 = d((0, 1)); c1 = d((1, 1)) - c2 - c0
    sols = []
    if abs(c2) < 1e-12:
        sols.append(((1, 0), 1))
        if abs(c1) > 1e-12:
            sols.append(((-c0 / c1, 1), 1))
    else:
        disc = c1*c1 - 4*c2*c0
        if abs(disc) < 1e-9:
            sols.append(((-c1/(2*c2), 1), 2))
        else:
            r = cmath.sqrt(disc)
            sols += [(((-c1 + r)/(2*c2), 1), 1), (((-c1 - r)/(2*c2), 1), 1)]
    tot = 0
    for s, mult in sols:
        if s[1] != 0 and root_index(s[0]) is not None:
            continue  # blown-up point; no tangency possible in a finite group (checked below)
        a = tvec(f1, LAMS[k1], s); b = tvec(f2, LAMS[k2], s)
        rho = b[0]/a[0] if abs(a[0]) > abs(a[1]) else b[1]/a[1]
        w1 = wval(f1, LAMS[k1], e1, s) * rho**2
        w2 = wval(f2, LAMS[k2], e2, s)
        assert abs(w1) > 1e-9
        if close(w1, w2):
            tot += mult
        else:
            assert close(w1, -w2)
    return tot


def inter(c1, c2):
    t1, x1 = c1; t2, x2 = c2
    if t1 > t2 or (t1 == t2 and False):
        pass
    key = {t1, t2}
    if t1 == t2 and x1 == x2:
        return -2
    if t1 == 'N' and t2 == 'N':
        return 0
    if t1 == 'N' and t2 == 'T': return 1 if x1[0] == x2 else 0
    if t1 == 'T' and t2 == 'N': return 1 if x2[0] == x1 else 0
    if t1 == 'N' and t2 == 'U': return 1 if x1[1] == x2 else 0
    if t1 == 'U' and t2 == 'N': return 1 if x2[1] == x1 else 0
    if t1 in 'TU' and t2 in 'TU':
        return 0
    if t1 == 'G' and t2 == 'G':
        return gg(x1, x2)
    if t1 == 'G':
        c1, c2 = c2, c1; t1, x1, t2, x2 = t2, x2, t1, x1
    # now c2 is graph
    fam, k, eps = x2
    if t1 in 'TU':
        return 0
    a, b = x1
    return 1 if phi_on_root(fam, LAMS[k], a) == b else 0


Gm = Matrix(n, n, lambda i, j: inter(curves[i], curves[j]))
assert Gm == Gm.T
print('rank of Gram of 40 curves:', Gm.rank())

# Galois action on curves: generators s_beta, s_i, s_theta
def act(gen, c):
    t, x = c
    def rt(a):
        if gen == 'b': return [1, 0, 3, 2][a]
        if gen == 'i': return [0, 1, 3, 2][a]
        return a
    if t == 'N': return ('N', (rt(x[0]), rt(x[1])))
    if t == 'T': return ('T', rt(x))
    if t == 'U': return ('U', rt(x))
    fam, k, eps = x
    if gen == 'i':
        k2 = [0, 3, 2, 1][k]
        return ('G', (fam, k2, -eps if fam == 1 else eps))
    if gen == 't':
        return ('G', (fam, k, -eps))
    return c

idx = {c: i for i, c in enumerate(curves)}
# basis: choose 20 independent curves
basis = []
for i in range(n):
    if Matrix([list(Gm.row(j)) for j in basis + [i]]).rank() > len(basis):
        basis.append(i)
assert len(basis) == 20
GB = Gm.extract(basis, basis)
print('disc of span of basis curves:', GB.det())
# coordinates of every curve in the basis (rational)
GBinv = GB.inv()
coords = {}
for i in range(n):
    v = GBinv * Gm.extract(basis, [i])
    coords[i] = v
# lattice L spanned by all 40 curves: find Z-basis via HNF of denominators
den = ilcm(*[x.q for i in range(n) for x in coords[i]])
rows = Matrix([[int(x * den) for x in coords[i]] for i in range(n)])
from sympy.matrices.normalforms import hermite_normal_form
H = hermite_normal_form(rows.T).T  # rows generate
H = Matrix([list(H.row(i)) for i in range(H.rows) if any(H.row(i))])
Lb = H / den  # rows: Z-basis of L in basis-curve coordinates
GL = Lb * GB * Lb.T
print('rank L', GL.rank(), 'disc L', GL.det())

# Galois matrices on Q^20 (coordinates w.r.t. basis curves)
def galmat(gen):
    cols = [coords[idx[act(gen, curves[b])]] for b in basis]
    return Matrix.hstack(*cols)

for gname in 'bit':
    Mg = galmat(gname)
    assert Mg.T * GB * Mg == GB, gname
print('Galois acts isometrically')

import json
json.dump({'GB': [[int(x) for x in GB.row(i)] for i in range(20)],
           'Lb': [[str(x) for x in Lb.row(i)] for i in range(Lb.rows)],
           'gal': {g: [[str(x) for x in galmat(g).row(i)] for i in range(20)] for g in 'bit'},
           'basis': [str(curves[b]) for b in basis]},
          open('scratch/rv-elim3/k1_b-7/ns_data.json', 'w'))
print('saved')
