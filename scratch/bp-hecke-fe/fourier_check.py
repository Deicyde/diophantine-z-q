# Finite Fourier transform of the character data c_d on (Z/4d)^2 (for the functional equation).
# g2(nu) = sum_{j mod 4} unitOf(j) e(j.nu/4);  odd part: sum_{j mod d} chi_d(Nj) e(j.nu/d) vs d*chi_d(N nu).
import cmath, itertools
import cypari2
pari = cypari2.Pari()
def unit(a, b):
    t = (a % 4, b % 4)
    if t in [(1,0),(3,2)]: return 1
    if t in [(3,0),(1,2)]: return -1
    if t in [(0,3),(2,1)]: return 1j
    if t in [(0,1),(2,3)]: return -1j
    return 0
e = lambda x: cmath.exp(2j*cmath.pi*x)
r = lambda z: complex(round(z.real, 9), round(z.imag, 9))
print("g2(nu) for nu mod 4 (nonzero values):")
for n1, n2 in itertools.product(range(4), repeat=2):
    g = sum(unit(a, b) * e((a*n1 + b*n2)/4) for a in range(4) for b in range(4))
    if abs(g) > 1e-9:
        # compare with unit(mu) where nu = (1+i) mu  (mu = nu/(1+i) = nu (1-i)/2)
        mu = complex(n1, n2) * (1 - 1j) / 2
        print("  nu=(%d,%d)  g2=%s  mu=nu/(1+i)=%s  unit(mu)=%s" % (n1, n2, r(g), mu, unit(int(mu.real), int(mu.imag))))
for d in [5, 13, 21, 3, 7]:
    bad = 0
    for n1, n2 in itertools.product(range(d), repeat=2):
        S = sum(int(pari.kronecker(a*a + b*b, d)) * e((a*n1 + b*n2)/d) for a in range(d) for b in range(d))
        if abs(S - d * int(pari.kronecker(n1*n1 + n2*n2, d))) > 1e-6: bad += 1
    print("odd part d=%d: #nu with S != d*chi_d(N nu): %d" % (d, bad))
