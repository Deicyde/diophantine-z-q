# Check: a_n(C_d) = (1/4) * sum_{a^2+b^2=n} chi_d(a^2+b^2) * unit(a mod 4, b mod 4) * (a+bi)
# chi_d(m) = Jacobi symbol (m/d); unit as in Hecke.lean (`unitOf`). PARI ellan for a_n.
import cypari2
pari = cypari2.Pari()
def unit(a, b):
    t = (a % 4, b % 4)
    if t in [(1,0),(3,2)]: return 1
    if t in [(3,0),(1,2)]: return -1
    if t in [(0,3),(2,1)]: return 1j
    if t in [(0,1),(2,3)]: return -1j
    return 0
NMAX = 400
for d in [1, 5, 13, 21, 29, 37, 53, 85]:
    E = pari.ellinit([0, 0, 0, -d*d, 0])
    an = [int(x) for x in pari.ellan(E, NMAX)]
    bad = 0
    for n in range(1, NMAX+1):
        s = 0
        r = int(n**0.5) + 1
        for a in range(-r, r+1):
            for b in range(-r, r+1):
                if a*a + b*b == n:
                    s += int(pari.kronecker(n, d)) * unit(a, b) * complex(a, b)
        s /= 4
        if abs(s - an[n-1]) > 1e-9:
            bad += 1
            if bad < 4: print("  mismatch d=%d n=%d an=%d formula=%s" % (d, n, an[n-1], s))
    print("d=%d  n<=%d  mismatches=%d  cond=%s rootno=%s" % (d, NMAX, bad, pari.ellglobalred(E)[0], pari.ellrootno(E)))
