"""Degrees over Q of the coordinates of f0(P_n) and z_n = (1-[i]) f0(P_n), n = 5 (mod 8):
TYZ Prop 3.2(1) predicts [Q(z_n) H_n : Q] = [H'_n : Q] = 4 h(-4n), and f0(P_n) generating H_{n,4}
(degree 2 h(-64n) = 8 h(-4n))."""
from heeg import *
from sigma5 import iP, sub
def exact_deg(v, dmax):
    for dd in range(2, dmax+1):
        pol = pari.algdep(v, dd)
        if pari.poldegree(pol) == dd and abs(pari.subst(pol, 'x', v)) < pari('1e-300'):
            return dd, pol
    return None, None
out=[]
for n in [5, 13, 21]:
    D = -64*n; hK = int(pari.qfbclassno(-4*n))
    P0 = xy(tau_of(16*(n+1), -8, D)); z = sub(P0, iP(P0))
    r = []
    for nm, v in (('x f0', P0[0]), ('y f0', P0[1]), ('x z', z[0]), ('y z', z[1])):
        d, pol = exact_deg(v, 8*hK)
        r.append(f'{nm}: {d}')
    s = f'n={n} h(-4n)={hK}: ' + ', '.join(r); print(s); out.append(s)
open('degrees5.out','w').write('\n'.join(out)+'\n')
