"""TYZ Lemma 3.21(4) (Period7.tex L2514-2516) for the pinned class-7 genus point
Z(e) = sum_{t in 2Cl_e} z_e^t, z_e = Heegner point of [(e+delta^2)/4, delta, 1] (delta least in
[0,128) with delta^2 = -e mod 128), and t(z_e) computed as the Heegner points of the classes in
2Cl_e (Shimura reciprocity; any direction, 2Cl is a group).  Z(e) lies in the genus field
L_e = Q(sqrt(p*) : p | e); write its coordinates in the basis prod sqrt(p*), apply a lift beta' of
beta_1 = r_inf(-1) r_2(-2) via cm-points' betaOneSign (Package.lean), and check
   Z(e)^{beta'} + Z(e) = g(e) * tau(1/2),  tau(1/2) = T = (2, -4)  (Lean: tauG 1 = ptT)."""
from itertools import combinations
from heeg import *
from class7 import deltas, add

def betaOneSign(D):
    v = D//2 if D % 2 == 0 else D
    s1 = -1 if D < 0 else 1
    s2 = 1 if v % 8 in (1, 3) else -1
    return s1*s2

def mul(k, P):
    R = None
    for _ in range(k):
        R = P if R is None else (None if P is None else add(R, P)) if R is not None else P
    return R

def factor_primes(n):
    return [int(p) for p in pari.factor(n)[0]]

T = (pari(2), pari(-4))
out = []
def say(*a):
    s = ' '.join(str(t) for t in a); print(s); out.append(s)

for e in [7, 15, 23, 31, 39, 47, 55, 71, 79, 87, 95, 103]:
    D = -e
    d0 = deltas(e)[0]
    reps = heegner_reps(D, d0)
    pts = {r: xy(tau_of(a, b, D)) for r, (a, b, c) in reps.items()}
    squares = set()
    for r in pts:
        s = pari.qfbred(pari.Qfb(*r)**2)
        squares.add(tuple(int(t) for t in pari.Vec(s)[:3]))
    sq = [r for r in pts if r in squares]
    g = len(sq)
    Z = None
    for r in sq:
        Z = pts[r] if Z is None else add(Z, pts[r])
    ps = factor_primes(e)
    pstar = [p if p % 4 == 1 else -p for p in ps]
    basis = []
    for k in range(len(pstar)+1):
        for c in combinations(pstar, k):
            Dp = 1
            for t in c: Dp *= t
            basis.append(Dp)
    sq_vals = [pari(f"sqrt({Dp})") for Dp in basis]   # principal roots
    conjZ = []
    ok = True
    for coord in Z:
        v = [coord] + sq_vals
        rel = pari.lindep(v)
        c0 = rel[0]
        coeffs = [-rel[j+1]/c0 for j in range(len(basis))]
        resid = abs(coord - sum(cf*sv for cf, sv in zip(coeffs, sq_vals)))
        if resid > pari('1e-300') or c0 == 0:
            ok = False
        conjZ.append(sum(cf*betaOneSign(Dp)*sv for cf, Dp, sv in zip(coeffs, basis, sq_vals)))
        say(f'  e={e}: coord = ' + ' + '.join(f'({cf})*sqrt({Dp})' for cf, Dp in zip(coeffs, basis) if cf != 0) + f'   resid {float(resid):.1e}')
    S = add(tuple(conjZ), Z)
    gT = mul(g % 4, T) if g % 4 else None
    if S is None:
        verdict = (gT is None)
        say(f'e={e} g={g}: Z^b+Z = O ; g*T = {gT} ; match {verdict} ; basis ok {ok}')
    else:
        dist = abs(S[0]-gT[0]) + abs(S[1]-gT[1]) if gT is not None else 'inf'
        say(f'e={e} g={g} signs={[betaOneSign(Dp) for Dp in basis]}: Z^b+Z = ({pari.precision(S[0],20)}, {pari.precision(S[1],20)}) ; g*T = {gT} ; |diff| = {float(dist) if dist != "inf" else dist:.1e} ; basis ok {ok}')
open('lemma321_7.out', 'w').write('\n'.join(out) + '\n')
