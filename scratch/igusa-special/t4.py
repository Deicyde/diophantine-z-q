import sys, itertools, time, pickle; sys.path.insert(0, '.')
from poly import *
y = load_y(); J = load_J()
nv = 3
E1, E2, E3 = var(0, nv), var(1, nv), var(2, nv); one = const(1, nv)
# x(x-1)(x^3 - e1 x^2 + e2 x - e3): coeffs c0..c6
N = [{}, E3, scal(-1, add(E2, E3)), add(E1, E2), scal(-1, add(one, E1)), one, {}]
Y = [[subst(cc, N, nv) for cc in row] for row in y]
print('Y(e) sizes', [[len(t) for t in row] for row in Y])
def det3(M):
    return add(add(mul(M[0][0], sub(mul(M[1][1], M[2][2]), mul(M[1][2], M[2][1]))),
                   scal(-1, mul(M[0][1], sub(mul(M[1][0], M[2][2]), mul(M[1][2], M[2][0]))))),
               mul(M[0][2], sub(mul(M[1][0], M[2][1]), mul(M[1][1], M[2][0]))))
D = det3(Y); print('det(e) size', len(D))
# synthemes in l,m,n
L = [var(i, 3) for i in range(3)]
def quad(p, q):
    if p == 'inf': return [scal(-1, q), one, {}]
    return [mul(p, q), scal(-1, add(p, q)), one]
def synthemes(pts):
    if not pts: yield []; return
    a = pts[0]
    for i in range(1, len(pts)):
        rest = pts[1:i] + pts[i+1:]
        for s in synthemes(rest): yield [(a, pts[i])] + s
pts = ['inf', {}, one, L[0], L[1], L[2]]
names = ['inf', '0', '1', 'l', 'm', 'n']
syn = list(synthemes(list(range(6))))
def Dof(s): return det3([quad(pts[a], pts[b]) for a, b in s])
# classes under S3 on l,m,n (indices 3,4,5)
def canon(s):
    best = None
    for perm in itertools.permutations([3, 4, 5]):
        mp = {0:0, 1:1, 2:2, 3:perm[0], 4:perm[1], 5:perm[2]}
        t = tuple(sorted(tuple(sorted((mp[a], mp[b]))) for a, b in s))
        best = t if best is None or t < best else best
    return best
cls = {}
for s in syn: cls.setdefault(canon(s), []).append(s)
T = []
for c, ss in cls.items():
    pr = const(1, 3)
    for s in ss: pr = mul(pr, Dof(s))
    te = sym_to_e(pr)
    print([[names[a]+names[b] for a, b in s] for s in ss][0], len(ss), 'prod terms', len(pr), 'in e', len(te), 'D rep', Dof(ss[0]))
    T.append(te)
prod = const(1, 3)
for t in T: prod = mul(prod, t)
ratio = None
for k in D:
    r = D[k] / prod.get(k, F(0)) if prod.get(k) else None
    ratio = r; break
print('ratio', ratio, sub(D, scal(ratio, prod)) == {})
pickle.dump((N, Y, D, T, cls), open('/tmp/igs_t4.pkl', 'wb'))
