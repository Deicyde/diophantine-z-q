import sys, pickle, itertools; sys.path.insert(0, '.')
from poly import *
N, Y, D, T, cls = pickle.load(open('/tmp/igs_t4.pkl', 'rb'))
J = load_J()
nv = 3
l, m, n = [var(i, nv) for i in range(3)]; one = const(1, nv)
e = [add(add(l, m), n), add(add(mul(l, m), mul(l, n)), mul(m, n)), mul(mul(l, m), n)]
Dc = {1: lambda l, m, n: sub(mul(m, n), l),
      2: lambda l, m, n: add(sub(sub(l, m), n), mul(m, n)),
      3: lambda l, m, n: add(sub(sub(l, mul(l, m)), mul(l, n)), mul(m, n)),
      4: lambda l, m, n: add(sub(sub(mul(l, m), l), mul(l, n)), n)}
perms = {1: [(0,1,2), (1,0,2), (2,0,1)], 2: [(0,1,2), (1,0,2), (2,0,1)], 3: [(0,1,2), (1,0,2), (2,0,1)],
         4: [(0,1,2), (0,2,1), (1,0,2), (1,2,0), (2,0,1), (2,1,0)]}
L = [l, m, n]
for c in range(1, 5):
    Tc = subst(T[c-1], e, nv)
    pr = one
    for p in perms[c]: pr = mul(pr, Dc[c](*[L[i] for i in p]))
    k0 = next(iter(Tc)); ratio = Tc[k0] / pr.get(k0, F(1))
    print(c, 'ratio', ratio, sub(Tc, scal(ratio, pr)) == {})
# J10 of Ne
E1, E2, E3 = [var(i, 3) for i in range(3)]
Ne = [{}, E3, scal(-1, add(E2, E3)), add(E1, E2), scal(-1, add(one, E1)), one, {}]
J10Ne = subst(J[3], Ne, 3)
print('J10(Ne) terms', len(J10Ne))
open('gen_J10Ne.txt', 'w').write(lean_poly(J10Ne, ['e1', 'e2', 'e3']))
J10Nr = subst(J10Ne, e, 3)
disc = one
for a, b in [(l, {}), (m, {}), (n, {}), (l, one), (m, one), (n, one), (l, m), (l, n), (m, n)]:
    dd = sub(a, b); disc = mul(disc, mul(dd, dd))
k0 = next(iter(J10Nr)); ratio = J10Nr[k0] / disc[k0]
print('J10 Nr ratio', ratio, sub(J10Nr, scal(ratio, disc)) == {})
