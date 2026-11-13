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

# Full CdFourier as defined in HeckeFE.lean: for nu mod M=4d,
#   fourierHat(nu) = sum_{j in [0,M)^2} cdChar(j) e((j1 nu1 + j2 nu2)/M),
#   cdChar(j) = (N j / d) * unitOf(j mod 4);
# claim: nu1+nu2 odd -> 0;  nu = (m1-m2, m1+m2) -> 4d(1+i)(2/d) cdChar(m).
print("full CdFourier check:")
for d in [5, 13, 21]:
    M = 4*d
    jac2 = int(pari.kronecker(2, d))
    cd = {}
    for a in range(M):
        for b in range(M):
            cd[(a, b)] = int(pari.kronecker(a*a + b*b, d)) * unit(a, b)
    ex = [e(k / M) for k in range(M)]
    bad = 0
    for n1 in range(M):
        for n2 in range(M):
            F = sum(cd[(a, b)] * ex[(a*n1 + b*n2) % M] for a in range(M) for b in range(M) if cd[(a, b)] != 0)
            if (n1 + n2) % 2 == 1:
                ok = abs(F) < 1e-6
            else:
                # mu with (mu1-mu2, mu1+mu2) = nu mod M: mu1=(n1+n2)/2, mu2=(n2-n1)/2 (mod M/... use exact ints)
                m1, m2 = (n1 + n2) // 2, (n2 - n1) // 2
                ok = abs(F - 4*d*(1+1j)*jac2*cd[(m1 % M, m2 % M)]) < 1e-6
            if not ok: bad += 1
    print("  d=%d M=%d (2/d)=%d  failures over all nu mod M: %d" % (d, M, jac2, bad))
