# X3c: does the M1 theta=1 curve C_m: y^2 = -m R0^3 q^4 + 2 m R0^2 q^2 + (m^2 T^2 - m R0) have points?
# Toy instances: R0 = |F(n)| (2730^6 dropped; it only rescales), T random rational, m in DL8.
# For each (n, T, m): Jacobian via ellfromeqn, rank bounds via ellrank, and point search
# hyperellratpoints(f, 2000). 30 instances, run sequentially.
import random, cypari2
pari = cypari2.Pari(); pari.allocatemem(10**9); random.seed(5)
def F(n): return n*(n+15)*(n+20)*(n+24)*(n+30)*(n+60)
S8 = [f*m0 for f in (1, 2) for m0 in (1, 3, 5, 7)]
ns = [n for n in range(1, 60) if F(n) != 0][:30]
tot_inst = inst_pt = 0; ranks = {}
for n in ns:
    R0 = abs(F(n)); T = pari(random.randint(1, 3000)) / random.randint(1, 300)
    found = False; rk = []
    for m in S8:
        f = pari(f'(-{m}*{R0}^3)*x^4 + 2*{m}*{R0}^2*x^2 + ({m}^2*({T})^2 - {m}*{R0})')
        den = pari.denominator(pari.content(f)); fi = f * den**2           # y -> y*den
        try:
            E = pari.ellinit(pari.ellfromeqn(pari('y^2') - fi))
            r = pari.ellrank(E, 1); lo, hi = int(r[0]), int(r[1])
        except Exception as e:
            lo, hi = -1, -1
        pts = pari.hyperellratpoints(fi, 2000)
        rk.append((m, lo, hi, len(pts)))
        ranks[(lo, hi)] = ranks.get((lo, hi), 0) + 1
        if len(pts): found = True
    tot_inst += 1; inst_pt += found
    print(n, T, [x for x in rk if x[3] or x[1] > 0 or x[2] == 0][:8], flush=True)
print("instances with a point of height <= 2000 for some m in DL8:", inst_pt, "/", tot_inst)
print("rank bound histogram (lo,hi): count over 240 curves:", ranks)
