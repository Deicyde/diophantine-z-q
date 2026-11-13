import sys, random, itertools; sys.path.insert(0, '.')
from poly import *
y = load_y(); J = load_J()
def polymul_x(c, d):
    r = [F(0)]*(len(c)+len(d)-1)
    for i, a in enumerate(c):
        for j, b in enumerate(d): r[i+j] += a*b
    return r
def coeffs_from_roots(rs, lead=1):
    c = [F(lead)]
    for r in rs: c = polymul_x(c, [F(-r), F(1)])
    return c + [F(0)]*(7-len(c))
def det3(m):
    return (m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1]) - m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0])
            + m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0]))
def detyv(a): return det3([[ev(c, a) for c in r] for r in y])
def quad(p, q):
    if p == 'inf': return [F(-q), F(1), F(0)]
    if q == 'inf': return [F(-p), F(1), F(0)]
    return [F(p*q), F(-(p+q)), F(1)]
def synthemes(pts):
    if not pts: yield []; return
    a = pts[0]
    for i in range(1, len(pts)):
        rest = pts[1:i] + pts[i+1:]
        for s in synthemes(rest): yield [(a, pts[i])] + s
random.seed(1)
for t in range(4):
    l, m, n = [F(random.randint(-30, 30), random.randint(1, 9)) for _ in range(3)]
    a = coeffs_from_roots([0, 1, l, m, n])
    d = detyv(a)
    prod = F(1)
    for s in synthemes(['inf', 0, 1, l, m, n]):
        prod *= det3([quad(*pr) for pr in s])
    print(d / prod if prod else None, J and ev(J[3], a))
