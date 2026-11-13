import sys, itertools, time; sys.path.insert(0, '.')
from poly import *
y = load_y(); J = load_J()
nv = 3
l, m, n = var(0, nv), var(1, nv), var(2, nv)
one = const(1, nv)
def pmul(c, d):
    r = [{}]*(len(c)+len(d)-1)
    for i, a in enumerate(c):
        for j, b in enumerate(d): r[i+j] = add(r[i+j], mul(a, b))
    return r
c = [one]
for r in [const(0, nv), one, l, m, n]:
    c = pmul(c, [scal(-1, r), one])
N = c + [{}]
print('N sizes', [len(t) for t in N])
t0 = time.time()
Y = [[subst(cc, N, nv) for cc in row] for row in y]
print('Y sizes', [[len(t) for t in row] for row in Y], [[max(deg(t, i) for i in range(3)) for t in row] for row in Y], time.time()-t0)
def det3(M):
    return add(add(mul(M[0][0], sub(mul(M[1][1], M[2][2]), mul(M[1][2], M[2][1]))),
                   scal(-1, mul(M[0][1], sub(mul(M[1][0], M[2][2]), mul(M[1][2], M[2][0]))))),
               mul(M[0][2], sub(mul(M[1][0], M[2][1]), mul(M[1][1], M[2][0]))))
t0 = time.time()
D = det3(Y)
print('det size', len(D), [deg(D, i) for i in range(3)], time.time()-t0)
import pickle; pickle.dump((N, Y, D), open('/tmp/igs_t3.pkl', 'wb'))
