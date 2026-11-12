"""Absolute test of Thm 3.3 for d1 = 1: P_1(n) = eps 2^{h2(n)} PP(n), PP(n) = 2^{-1-rho(n)} L(n) alpha_n.
Index of 4 P_1(n) over a generator alpha_n of A(K_n)^- (= A_n(Q), A_n: 2n v^2 = u^3 + u ~ Y^2 = X^3 + 4n^2 X)
is predicted to be 2^{h2(n)+1-rho(n)} |L(n)|.  rho from 4^rho = 2 h(alpha_n) / h(g_n), g_n generator of E_n(Q)."""
import sys; sys.path.insert(0, '.')
from tmany import *


def run(n):
    if n % 8 == 5:
        S, h = S_sums(n, [1, n], -8, -64 * n)
        z4 = S[1] - I * S[n]
    else:
        S, h = S_sums(n, [1], delta7(n), -n)
        z4 = 4 * S[1]
    Cn = pari('ellinit([0,0,0,4*%d^2,0])' % n)
    rk = pari.ellrank(Cn)
    gens = pari.ellsaturation(Cn, rk[3], 200)
    En = pari('ellinit([0,0,0,-%d^2,0])' % n)
    rkE = pari.ellrank(En)
    gE = pari.ellsaturation(En, rkE[3], 200)
    assert rk[0] == 1 and rk[1] == 1 and len(gens) == 1 and len(gE) == 1, (n, rk, rkE)
    ha = pari.ellheight(Cn, gens[0]); hg = pari.ellheight(En, gE[0])
    four_rho = 2 * ha / hg
    rho = round(float(pari.log(four_rho) / pari.log(4)))
    assert abs(float(four_rho) - 4 ** rho) < 1e-20, (n, four_rho)
    Lp = pari('lfun(ellinit([0,0,0,-%d^2,0]),1,1)' % n)
    L2 = Lp / (2 ** (2 * kodd(n) - 3) * OM1 / pari.sqrt(n) * hg)
    Ln = round(float(L2) ** 0.5)
    assert abs(float(L2) - Ln ** 2) < 1e-15, (n, L2)
    al = gens[0]                       # (X'', Y'') on Y^2 = X^3 + 4 n^2 X  ->  X = -X''/n, Y = sqrt(-n) Y''/n^2 on 32a1
    Xa = -al[0] / n
    Ya = pari('sqrt(-%d)' % n) * al[1] / n ** 2
    za = pari('(P) -> ellpointtoz(E32, P)')([Xa, Ya])
    hits = [m for m in range(-512, 513) if in_lattice(4 * (z4 - m * za), 1e-30)]
    idx = abs(hits[0]) if len(hits) == 1 else -1
    pred = 2 ** (h2(n) + 1 - rho) * Ln
    print("n=%-4d h2=%d rho=%d L(n)=%d  index[4P_1(n) : alpha_n] = %s  predicted 2^(h2+1-rho) L = %d  %s"
          % (n, h2(n), rho, Ln, hits, pred, idx == pred))
    sys.stdout.flush()


for a in sys.argv[1:]:
    try:
        run(int(a))
    except Exception as ex:
        print('n=%s FAILED: %r' % (a, ex)); sys.stdout.flush()
