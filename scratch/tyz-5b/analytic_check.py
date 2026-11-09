"""Numerical sanity check of the conclusion: for small slot-type n = p q0 (p = 7 mod 8 prime,
q0 = 3 mod 8 the least prime with the slot symbol), ellanalyticrank of C_n and a point with x in pQ^2."""
import cypari2, sys
pari = cypari2.Pari(); pari.allocatemem(2 * 10 ** 9)
def leg(a, p): return 0 if pow(a % p, (p - 1) // 2, p) == 1 else 1
PR = [int(p) for p in pari.primes(400)][1:]
out = 0
for p in PR:
    if p % 8 != 7: continue
    for s in (0, 1):
        beta = -p if s else p; x = (s + 1) % 2
        q0 = next(q for q in PR if q % 8 == 3 and leg(q, p) == x)
        n = beta * q0
        E = pari.ellinit([0, 0, 0, -n * n, 0])
        ar = pari.ellanalyticrank(E)
        rk = pari.ellrank(E, 2)
        hit = any(len(c) == 2 and c[0] != 0 and int(pari.issquare(pari(c[0]) / beta)) == 1
                  for P in rk[3] for c in [P] + [pari.elladd(E, P, t) for t in ([0, 0], [n, 0], [-n, 0])])
        print(f"beta={beta} q0={q0} |n|={abs(n)} |n|%8={abs(n)%8} analytic rank={int(ar[0])} L^(r)/r!={float(ar[1]):.4f} ellrank={rk[:3]} point x in beta Q^2: {hit}")
        out += 1
        if out >= 12: sys.exit()
