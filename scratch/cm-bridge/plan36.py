"""Checks for the follow-up plan `TYZThm36Seven ⇐ ShimuraReciprocityPic + EtaModelFricke` (report §2, Bridge.lean §14):
for squarefree n = 7 (mod 8), d = tyzDelta n, A = (n+d^2)/4:
 (a) Q' = [32, d, (n+d^2)/128] is a Heegner form (level 32, disc -n) and tau_{Q'} = W(tau_{conj Q}),
     W(t) = -1/(32 t), conj Q = [A, -d, 1];
 (b) its Heegner point equals the Heegner point of the class [p2]^5 (B = d mod 64) used in thm36_7.py,
     and equals T - conj(z_n)  (T = (2,-4))."""
from heeg import *
from thm36_7 import add, conjP, dist, red
T = (pari(2), pari(-4))
out = []
def say(s): print(s); out.append(s)
for n in [7, 15, 23, 31, 39, 47, 55, 71]:
    D = -n
    d = [t for t in range(128) if (t*t + n) % 128 == 0][0]
    A = (n + d*d)//4
    assert (n + d*d) % 128 == 0
    C2 = (n + d*d)//128
    tauQc = tau_of(A, -d, D)                 # conj Q = [A, -d, 1]
    tauQ2 = tau_of(32, d, D)
    wt = -1/(32*tauQc)
    z = xy(tau_of(A, d, D))
    zq2 = xy(tauQ2)
    reps = heegner_reps(D, d)
    b0 = d % 4
    P2 = pari.Qfb(2, b0, (b0*b0 + n)//8)
    Ar, Br, Cr = reps[red(P2**5)]
    zc = xy(tau_of(Ar, Br, D))
    negconj = add(T, (pari.conj(z[0]), -pari.conj(z[1])))   # T - conj z
    say(f"n={n} d={d}: |W(tau_conjQ) - tau_Q'| = {float(abs(wt - tauQ2)):.1e}; "
        f"|z_Q' - z_[p2]^5| = {dist(zq2, zc):.1e}; |z_Q' - (T - conj z)| = {dist(zq2, negconj):.1e}; "
        f"[32,d,{C2}] reduced = {red(pari.Qfb(32, d, C2))}, [p2]^5 = {red(P2**5)}")
open('plan36.out', 'w').write('\n'.join(out) + '\n')
