"""Numerical check of cm-points' leaf Package.TYZSigmaFixesZn and of TYZ Prop 3.2(1) for class 5.
n = 5 (mod 8) squarefree; f0(P_n) = Heegner point of tyzForm n = [16(n+1), -8, 1] (disc -64n);
z_n = (1 - [i]) f0(P_n), [i](x, y) = (-x, i y).
sigmaClass n = class in Pic(O_{n,4}) of (3 + 2 sqrt(-n)) O_K (RingClass.lean).  A prime
p = a^2 + n b^2 with a odd, b = 2 (mod 4) generates (a + b sqrt(-n)) = r (3 + 2 sqrt(-n)) mod 4 O_K
(r = 3a), so pp = (a + b sqrt -n) O_K cap O4 lies in sigmaClass, and Frob_pp acts on H_{n,4} as the
Artin symbol of sigmaClass (order 2, so the Artin normalization does not matter).  Its action on
f0(P_n) is given by CM.ShimuraReciprocity (direction checked in shimura.py): f0(P_n) -> P_{Q'},
Q' = pbar * Q.  Check: (1 - [i]) (P_{Q'} - P_Q) = 0, i.e. P_{Q'} - P_Q in {O, (0,0)}; and that the
field of x(z_n) has degree 4 h(-n) (= [H'_n : Q], TYZ Prop 3.2(1)) while x(f0(P_n)) has degree
2 h(-64 n) (= [H_{n,4} : Q])."""
from fractions import Fraction as Fr
from heeg import *
from shimura import pair_image
from class7 import add

def iP(P):
    return (-P[0], pari('I')*P[1])

def neg(P):
    return (P[0], -P[1])

def sub(P, Q):
    return add(P, neg(Q))

out = []
def say(*a):
    s = ' '.join(str(t) for t in a); print(s, flush=True); out.append(s)

if __name__ == "__main__":
 for n in [5, 13, 21, 29, 37]:
        D = -64*n
        Q = (16*(n+1), -8, 1)
        P0 = xy(tau_of(*Q[:2], D))
        zn = sub(P0, iP(P0))
        hK = int(pari.qfbclassno(-4*n)); h4 = int(pari.qfbclassno(D))
        d1 = pari.poldegree(pari.algdep(zn[0], 4*hK)); r1 = abs(pari.subst(pari.algdep(zn[0], 4*hK), 'x', zn[0]))
        d0 = pari.poldegree(pari.algdep(P0[0], 2*h4)); r0 = abs(pari.subst(pari.algdep(P0[0], 2*h4), 'x', P0[0]))
        say(f'n={n}: h(-4n)={hK} h(-64n)={h4}; deg x(z_n) <= {d1} (res {float(r1):.0e}), deg x(f0 P_n) <= {d0} (res {float(r0):.0e})')
        # minimal degree (search smaller degrees)
        for dd in range(2, 4*hK+1):
            pol = pari.algdep(zn[0], dd)
            if abs(pari.subst(pol, 'x', zn[0])) < pari('1e-350') and pari.poldegree(pol) == dd:
                say(f'   exact degree of x(z_n) over Q: {dd}; min poly {pol}'); break
        cnt = 0
        for a in range(1, 60, 2):
            for b in range(2, 60, 4):
                p = a*a + n*b*b
                if cnt >= 3 or not pari.isprime(p): continue
                bp = next(t for t in range(0, 2*p, 2) if (t - (-8*a*pow(b, -1, p))) % p == 0)
                assert (bp*bp - D) % (4*p) == 0
                Ilat = [(Fr(p), Fr(0)), (Fr(-bp, 2), Fr(-1, 2))]   # pbar = <p, (-b' - sqrt D)/2>, elements u + v sqrt D
                Qp = pair_image(Q, Ilat, D)
                P1 = xy(tau_of(*Qp[:2], D))
                dif = sub(P1, P0)
                if dif is None:
                    kind = 'O'
                elif abs(dif[0]) + abs(dif[1]) < pari('1e-350'):
                    kind = '(0,0)'
                else:
                    kind = f'OTHER x={pari.precision(dif[0],10)}'
                z1 = sub(P1, iP(P1))
                fixed = abs(z1[0]-zn[0]) + abs(z1[1]-zn[1])
                say(f'   p={p}=({a})^2+{n}({b})^2, b\'={bp}: Q\'={Qp}; P_Q\' - P_Q = {kind}; |rho(z_n) - z_n| = {float(fixed):.1e}; |P_Q\'-P_Q| = {float(abs(P1[0]-P0[0])):.2e}')
                cnt += 1
 open('sigma5.out', 'w').write('\n'.join(out) + '\n')
