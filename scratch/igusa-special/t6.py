import sys, pickle; sys.path.insert(0, '.')
from poly import *
# vars: u, v, r  (nv=3)
nv = 3
u, v, r = var(0, nv), var(1, nv), var(2, nv); one = const(1, nv)
def c(x): return const(x, nv)
def J4f(u, v): return add(add(scal(-128, v), scal(32, mul(u, u))), add(scal(2624, u), c(5280)))
def J10f(u, v):
    u2 = mul(u, u); u3 = mul(u2, u); u4 = mul(u3, u)
    terms = [(-262144, sub(mul(v, v), scal(2, u3))), (131072, mul(u2, v)), (-16384, u4), (2359296, mul(u, v)),
             (-1114112, u3), (-3538944, v), (-4423680, u2), (15925248, u), (-11943936, one)]
    s = {}
    for k, t in terms: s = add(s, scal(k, t))
    return s
# check against JE
JE = pickle.load(open('/tmp/igs_JE.pkl', 'rb'))
import random
for _ in range(3):
    A, B = F(random.randint(-9, 9)), F(random.randint(-9, 9))
    U, V = A*B, A**3+B**3
    assert ev(JE[1], (A, B)) == ev(J4f(c(U), c(V)), (0, 0, 0))
    assert ev(JE[3], (A, B)) == ev(J10f(c(U), c(V)), (0, 0, 0))
    assert ev(JE[2], (A, B)) == ev(sub(scal(128, J4f(c(U), c(V))), c(131072*(3*U+5))), (0,0,0))
print('J in (u,v) ok')
s = add(u, c(15))
# E3 cleared: J4 r^2 = 1024 (3 r s (1+r) - 40 (1+r+r^2))
rhs = scal(1024, sub(scal(3, mul(mul(r, s), add(one, r))), scal(40, add(add(one, r), mul(r, r)))))
E3 = sub(mul(J4f(u, v), mul(r, r)), rhs)
# v from E3: -128 v r^2 + (32u^2+2624u+5280) r^2 - rhs = 0 -> v = ((32u^2+2624u+5280) r^2 - rhs)/(128 r^2)
# work with V := 128 r^2 v  (so substitute v = Vn / (128 r^2)); clear denominators in E4 by r^?
Vn = sub(mul(add(add(scal(32, mul(u, u)), scal(2624, u)), c(5280)), mul(r, r)), rhs)
# u' = r s - 15 ; v' = (32u'^2+2624u'+5280 - r^2 J4)/128 ; J4 = rhs/r^2 on E3 => v' = (32u'^2+2624u'+5280)/128 - rhs/128
up = sub(mul(r, s), c(15))
vp = scal(F(1, 128), sub(add(add(scal(32, mul(up, up)), scal(2624, up)), c(5280)), rhs))
# J10(u,v) with v = Vn/(128 r^2): J10 is quadratic in v -> multiply by r^4
def J10_scaled(u, Vn, den):  # returns den^2 * J10(u, Vn/den)
    u2 = mul(u, u); u3 = mul(u2, u); u4 = mul(u3, u); d2 = mul(den, den)
    terms = [(-262144, sub(mul(Vn, Vn), scal(2, mul(u3, d2)))), (131072, mul(mul(u2, Vn), den)), (-16384, mul(u4, d2)),
             (2359296, mul(mul(u, Vn), den)), (-1114112, mul(u3, d2)), (-3538944, mul(Vn, den)), (-4423680, mul(u2, d2)),
             (15925248, mul(u, d2)), (-11943936, d2)]
    S = {}
    for k, t in terms: S = add(S, scal(k, t))
    return S
den = scal(128, mul(r, r))
G = sub(mul(J10f(up, vp), mul(den, den)), mul(pw(r, 5, nv), J10_scaled(u, Vn, den)))
print('G terms', len(G), 'deg u', deg(G, 0), 'deg v', deg(G, 1), 'deg r', deg(G, 2))
# test on D4 parametrisation
for t in [F(2), F(3, 7), F(-5, 2)]:
    print('D4 test', ev(G, (t*t, 0, F(16)/(1+t)**2)))
pickle.dump(G, open('/tmp/igs_G.pkl', 'wb'))
