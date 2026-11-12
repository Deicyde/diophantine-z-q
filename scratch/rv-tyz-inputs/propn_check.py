"""Consequence of I1-I7 (Proposition N, and reading A of TYZ Thm 3.5(2) for n = 5 mod 8) on samples.

mode 'full' n...:  n = 5 (mod 8) with T5a or T5b odd. Computes ord_{s=1} L(E_n,s) (PARI ellanalyticrank),
   a generator P of E_n(Q)/E_n[2] (ellrank + ellsaturation), calL(n)^2 = L'(E_n,1)/(2^{2k-3} Omega_n R_n)
   with R_n = 2 * NT height = PARI's ellheight (PARI normalises heights for BSD, i.e. twice the classical
   NT height; the choice R = 2*ellheight gives calL^2 = 1/2 on every sample, so integrality fixes R = ellheight), and rho(n) (2^rho = [E_n(Q) : phi_n(A_n(Q)) + E_n[2]], TYZ L381-388).
   Reading A of Thm 3.5(2) predicts: 2^{-rho} calL(n) is not even, i.e. v2(calL(n)) <= rho(n).
   Proposition N predicts: ord = 1.
mode 'rank' n...:  only ord_{s=1} (for large omega(n)).
"""
import sys, time
from tyzcalc import pari, primes_of, genus_sums, OMEGA_INT, nearest_square_root

mode = sys.argv[1]
ns = [int(a) for a in sys.argv[2:]]
gc = {}


def in_phi_image(xq, n):
    """Is the point with abscissa xq on E_n : n y^2 = x^3 - x in phi_n(A_n(Q)) (up to the sign of y)?"""
    disc = xq * xq - 1
    if not pari.issquare(disc):
        return False
    s = pari.sqrtint(pari.numerator(disc)) / pari.sqrtint(pari.denominator(disc))
    for u in (xq + s, xq - s):
        if u == 0:
            continue
        if pari.issquare((u ** 3 + u) / (2 * n)):
            return True
    return False


def v2(r):
    r = int(r)
    if r == 0:
        return 99
    v = 0
    while r % 2 == 0:
        r //= 2; v += 1
    return v


allok = True
for n in ns:
    t0 = time.time()
    assert n % 8 == 5 and pari.issquarefree(n)
    k = len(primes_of(n))
    T5a, T5b = genus_sums(n, gc)
    E = pari.ellinit([0, 0, 0, -n * n, 0])
    ar = pari.ellanalyticrank(E)
    r, Lr = int(ar[0]), ar[1]
    line = f'n={n} = {"*".join(map(str, primes_of(n)))} (k={k}): T5a={T5a} T5b={T5b} ord={r}'
    ok = (r == 1) if (T5a or T5b) else True
    if mode == 'full' and r == 1:
        rk = pari.ellrank(E)
        pts = [Q for Q in rk[3] if float(pari.ellheight(E, Q)) > 1e-9]
        if not pts:
            pts = [pari.ellheegner(E)]     # rank-1 curve: Heegner point of infinite order
        pts = pari.ellsaturation(E, pts, 200)
        # pick a point of infinite order; with rank 1, the saturated list spans E(Q)/tors
        P = None
        for Q in pts:
            if float(pari.ellheight(E, Q)) > 1e-9:
                P = Q
                break
        h = pari.ellheight(E, P)          # PARI normalisation
        Om = 2 / pari.sqrt(n) * OMEGA_INT
        base = Lr / (pari(2) ** (2 * k - 3) * Om)
        cand = {'R=2h': base / (2 * h), 'R=h': base / h}
        roots = {key: nearest_square_root(val, 1e-12) for key, val in cand.items()}
        # rho(n): P + T in phi(A_n(Q)) for some T in E[2]?
        rho = 1
        for T in ([0], [0, 0], [n, 0], [-n, 0]):
            Q = pari.elladd(E, P, T)
            if Q == [0]:
                continue
            xq = Q[0] / n                   # (X, Y) on y^2 = x^3 - n^2 x  ->  x = X/n on n y^2 = x^3 - x
            if in_phi_image(xq, n):
                rho = 0
                break
        line += (f'  hP={float(h):.6f}  calL^2 [R=2h]={float(cand["R=2h"]):.8f} [R=h]={float(cand["R=h"]):.8f}'
                 f'  -> calL={roots["R=h"]}  rho={rho}')
        cl = roots['R=h']
        if cl is not None and (T5a or T5b):
            okA = v2(cl) <= rho
            line += f'  readingA(v2(calL)<=rho): {"OK" if okA else "FAIL"}'
            ok = ok and okA
        else:
            line += '  (calL not integral)'
            ok = False
    allok &= ok
    print(line + f'  {"OK" if ok else "MISMATCH"}  ({time.time() - t0:.1f}s)', flush=True)
print('ALL OK' if allok else 'SOME MISMATCH')
