import sys, pickle; sys.path.insert(0, '.')
from poly import *
# vars u, v, rho, up(u'), vp(v')  nv=5
nv = 5
u, v, p = var(0, nv), var(1, nv), var(2, nv); one = const(1, nv); c = lambda x: const(x, nv)
r = mul(p, p); r2 = mul(r, r)
def J4f(u, v): return add(add(scal(-128, v), scal(32, mul(u, u))), add(scal(2624, u), c(5280)))
s = add(u, c(15))
E3 = sub(mul(r2, J4f(u, v)), scal(1024, sub(scal(3, mul(mul(r, s), add(one, r))), scal(40, add(add(one, r), r2)))))
hu = sub(mul(r, u), pw(sub(c(4), p), 2, nv))           # rho^2 u - (4-rho)^2
# target1: rho^4 v - 2 rho (4-rho)^3, times -128
T1 = scal(-128, sub(mul(pw(p, 4, nv), v), scal(2, mul(p, pw(sub(c(4), p), 3, nv)))))
rest = sub(T1, E3)
q, rem = divmod_lex(rest, hu, [0, 1, 2, 3, 4])
print('hv3: rem', rem, 'q terms', len(q))
names = ['u', 'v', 'ρ', "u'", "v'"]
# so T1 = E3 + q*hu  =>  -128*(rho^4 v - 2 rho (4-rho)^3) = E3 + q*hu
cert_v = q
# v' : V' = (32U'^2 + 2624U' + 5280 - r^2 J4(u,v))/128 where U' = r(u+15)-15; show V' = 2 (4rho-1)^3
Up = sub(mul(r, s), c(15))
Vp = scal(F(1, 128), sub(add(add(scal(32, mul(Up, Up)), scal(2624, Up)), c(5280)), mul(r2, J4f(u, v))))
T2 = sub(Vp, scal(2, pw(sub(scal(4, p), one), 3, nv)))
hv3 = sub(mul(pw(p, 3, nv), v), scal(2, pw(sub(c(4), p), 3, nv)))
q1, rem1 = divmod_lex(T2, hv3, [1, 0, 2, 3, 4])
q2, rem2 = divmod_lex(rem1, hu, [0, 1, 2, 3, 4])
print('vprime: rem', rem2, len(q1), len(q2))
open('gen_fam_certs.txt', 'w').write('cert_v (hv3: -128*(ρ^4 v - 2ρ(4-ρ)^3) = E3 + q*hu):\n' + lean_poly(cert_v, names, 100000) +
   '\n\nvprime: V\' - 2(4ρ-1)^3 = q1*hv3 + q2*hu:\nq1 = ' + lean_poly(q1, names, 100000) + '\nq2 = ' + lean_poly(q2, names, 100000) + '\n')
print(open('gen_fam_certs.txt').read())
