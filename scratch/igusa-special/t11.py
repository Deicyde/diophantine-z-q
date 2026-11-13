import sys, pickle; sys.path.insert(0, '.')
from poly import *
nv = 3
u, v, r = var(0, nv), var(1, nv), var(2, nv); one = const(1, nv); c = lambda x: const(x, nv)
def J4f(u, v): return add(add(scal(-128, v), scal(32, mul(u, u))), add(scal(2624, u), c(5280)))
def J10f(u, v):
    u2 = mul(u, u); u3 = mul(u2, u); u4 = mul(u3, u)
    terms = [(-262144, sub(mul(v, v), scal(2, u3))), (131072, mul(u2, v)), (-16384, u4), (2359296, mul(u, v)),
             (-1114112, u3), (-3538944, v), (-4423680, u2), (15925248, u), (-11943936, one)]
    s = {}
    for k, t in terms: s = add(s, scal(k, t))
    return s
s = add(u, c(15)); r2 = mul(r, r)
Up = sub(mul(r, s), c(15))
Vp = scal(F(1, 128), sub(add(add(scal(32, mul(Up, Up)), scal(2624, Up)), c(5280)), mul(r2, J4f(u, v))))
H10b = sub(J10f(Up, Vp), mul(pw(r, 5, nv), J10f(u, v)))
E3 = sub(mul(r2, J4f(u, v)), scal(1024, sub(scal(3, mul(mul(r, s), add(one, r))), scal(40, add(add(one, r), r2)))))
P = mul(pw(scal(128, r2), 2, nv), H10b)
q3, rem = divmod_lex(P, E3, [1, 2, 0])
print('rem has v?', any(k[1] for k in rem), 'q3 terms', len(q3))
Qf = add(sub(mul(r2, mul(u, u)), mul(scal(2, mul(r, add(c(16), r))), u)), pw(sub(c(16), r), 2, nv))
target = mul(mul(pw(r, 4, nv), pw(sub(one, r), 3, nv)), Qf)
# find constant ratio
k0 = next(iter(target)); ratio = rem[k0] / target[k0] if k0 in rem else None
print('ratio', ratio, sub(rem, scal(ratio, target)) == {})
names = ['u', 'v', 'r']
pickle.dump((q3, ratio), open('/tmp/igs_t11.pkl', 'wb'))
open('gen_q3.txt', 'w').write(lean_poly(q3, names, 100000))
# D4 checks: rho parametrisation
nv2 = 2
rho = var(0, 2); vv = var(1, 2)
print('q3 size', len(lean_poly(q3, names, 100000)))
