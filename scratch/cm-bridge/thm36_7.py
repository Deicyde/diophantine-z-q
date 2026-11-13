"""Numerical check of the leaf `TYZThm36Seven` (TYZ Thm 3.6(3), Period7.tex L1424-1427) in the Lean
formulation of `Bridge.lean` §12: for squarefree n = 7 (mod 8), z = z_n = Heegner point of
[(n+d^2)/4, d, 1] (d = tyzDelta n), p2 = (2, (sqrt(-n) - d)/2) (the place v_2 with
v_2(sqrt(-n) - d) >= 6), and rho acting on H_n as the arithmetic Artin symbol of [p2]^(-5)
(TYZ's geometric sigma_{varpi^5}):
      conj(z) + rho(z) = tau(1/2) = (2, -4).
rho(z) is computed by Shimura reciprocity in the direction VERIFIED by cm-numeric (shimura.out):
Art(b) maps the Heegner point of the class [a] (form [A,B,C] <-> a = (A, (-B+sqrt D)/2)) to that of
[a][b]^(-1); so rho(z) is the Heegner point (B = d mod 64) of the class [p2]^5.  Control: the class
[p2]^(-5) (wrong sign) and [p2]^5 with conj omitted."""
from heeg import *

def add(P, Q):
    if P is None: return Q
    if Q is None: return P
    (x1, y1), (x2, y2) = P, Q
    if abs(x1 - x2) < pari('1e-300'):
        if abs(y1 + y2) < pari('1e-300'):
            return None
        l = (3*x1**2 + 4)/(2*y1)
    else:
        l = (y2 - y1)/(x2 - x1)
    x3 = l**2 - x1 - x2
    return (x3, l*(x1 - x3) - y1)

def conjP(P):
    return (pari.conj(P[0]), pari.conj(P[1]))

def dist(P, Q):
    if P is None or Q is None: return 0 if P is Q else float('inf')
    return float(abs(P[0]-Q[0]) + abs(P[1]-Q[1]))

def red(f):
    v = pari.Vec(pari.qfbred(f))
    return reduce_form(int(v[0]), int(v[1]), int(v[2]))

T = (pari(2), pari(-4))
out = []
def say(s): print(s); out.append(s)

for n in [7, 15, 23, 31, 39, 47, 55, 71, 79, 87, 95, 103]:
    if not pari.issquarefree(n): continue
    D = -n
    d = [t for t in range(128) if (t*t + n) % 128 == 0][0]
    reps = heegner_reps(D, d)
    z = xy(tau_of((n + d*d)//4, d, D))
    b0 = d % 4
    P2 = pari.Qfb(2, b0, (b0*b0 + n)//8)
    cls = {}
    for e in (5, -5):
        r = red(P2**e) if e > 0 else red(pari.qfbpow(P2, e))
        A, B, C = reps[r]
        cls[e] = xy(tau_of(A, B, D))
    S = add(conjP(z), cls[5])
    Sw = add(conjP(z), cls[-5])
    order = int(pari.qfbclassno(D))
    say(f'n={n} h={order} d={d} [p2]^5={red(P2**5)}: |conj z + rho z - T| = {dist(S, T):.1e} ; '
        f'wrong sign [p2]^-5: {dist(Sw, T):.1e}')
open('thm36_7.out', 'w').write('\n'.join(out) + '\n')
