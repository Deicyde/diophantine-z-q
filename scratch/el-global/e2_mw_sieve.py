"""E2: reduction orders m_pi of P0 on E/K0, for primes pi of K0 of norm < NMAX (good reduction, pi not over 2, 7).
A label-based obstruction that uses L in A(Q) through local conditions at a fixed finite set of places is a
congruence condition on the index k mod some M; it is compatible with depth at pi (m_pi | k) whenever
gcd(m_pi, M) = 1. Output: fraction of pi with gcd(m_pi, M) = 1 for M = 2, 3, 6, 30, 210, and the fraction with
m_pi odd. Also checks the formal-group depth identity v_pi(x([k m_pi]P0)) = -2(v_p(k) + r_pi) on samples."""
import cypari2
pari = cypari2.Pari()
pari.allocatemem(2 * 10**9)
NMAX = 20000
pari("K = nfinit(y^2-2); d = 75-53*y; E = ellinit([0,0,0,-d^2,0], K); P0 = [(1641-1160*y)/8, (-123720+87483*y)/32];")
assert pari("ellisoncurve(E, P0)")
pari("""
mpi(pr) = {my(m = nfmodprinit(K, pr), a4 = nfmodpr(K, -d^2, m), x = nfmodpr(K, P0[1], m), yy = nfmodpr(K, P0[2], m),
  Ef = ellinit([0,0,0,a4,0], a4)); ellorder(Ef, [x, yy]);}
""")
pari(f"L = []; forprime(p = 3, {NMAX}, if(p == 7, next); dec = idealprimedec(K, p); for(i = 1, #dec, pr = dec[i]; if(pr.f == 2 && p^2 >= {NMAX}, next); L = concat(L, [[p, pr.f, mpi(pr)]])));")
rows = [(int(r[0]), int(r[1]), int(r[2])) for r in pari("L")]
print("primes pi:", len(rows))
from math import gcd
for M in (2, 3, 6, 30, 210):
    frac = sum(1 for _, _, m in rows if gcd(m, M) == 1) / len(rows)
    print(f"M={M:4d}: fraction gcd(m_pi, M) = 1: {frac:.4f}")
for f in (1, 2):
    sub = [m for _, ff, m in rows if ff == f]
    print(f"f={f}: {len(sub)} primes, fraction m_pi odd = {sum(1 for m in sub if m % 2) / max(1, len(sub)):.4f}")
# depth identity on 10 samples, p-adically at split p (sqrt2 in Q_p), both embeddings
PREC = 80
samples, out = 0, []
for p in [int(q) for q in pari("primes([11, 400])")]:
    if pari(f"kronecker(2, {p})") != 1 or p == 7: continue
    for sgn in (1, -1):
        s = pari(f"{sgn}*sqrt(2 + O({p}^{PREC}))")
        a4 = -(75 - 53*s)**2
        x0 = (1641 - 1160*s)/8; y0 = (-123720 + 87483*s)/32
        Ep = pari.ellinit([0, 0, 0, a4, 0])
        Ef = pari.ellinit([0, 0, 0, pari(f"Mod({pari.lift(pari.truncate(a4))}, {p})"), 0])
        m = int(pari.ellorder(Ef, [pari(f"Mod({pari.lift(pari.truncate(x0))}, {p})"), pari(f"Mod({pari.lift(pari.truncate(y0))}, {p})")]))
        v = []
        for k in (1, p, 2*p, p*p):
            Q = pari.ellmul(Ep, [x0, y0], k*m)
            v.append(int(pari.valuation(Q[0], p)))
        r = -v[0]//2
        ok = v[0] < 0 and v[0] % 2 == 0 and v[1] == v[2] == -2*(r+1) and v[3] == -2*(r+2)
        out.append((p, sgn, m, v, ok)); samples += 1
    if samples >= 10: break
for o in out: print("p=%d emb=%+d m=%d v_p(x([k m]P0)) for k=1,p,2p,p^2: %s ok=%s" % o)
print("depth identity v(x([km]P0)) = -2(v_p(k) + r) holds on all samples:", all(o[-1] for o in out))
