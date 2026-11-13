# Check the blueprint for GaussPointCount: S = sum_x chi2(x^3-x) = J(chi4,chi2) + conj, |J|^2 = p,
# and -J is primary (-J = 1 mod 2+2i), so S = -(pi + conj pi) with pi = -J primary.
import cypari2
pari = cypari2.Pari()
def primary(z):  # z = a+bi in Z[i] is = 1 mod (2+2i) iff (a,b) = (1,0),(3,2) mod 4
    a, b = int(round(z.real)), int(round(z.imag))
    return (a % 4, b % 4) in [(1, 0), (3, 2)]
for p in [5, 13, 17, 29, 37, 41, 53, 61, 73, 89]:
    g = int(pari.znprimroot(p).lift())
    log = {}; x = 1
    for k in range(p - 1):
        log[x] = k; x = x * g % p
    chi4 = lambda u: 0 if u % p == 0 else 1j ** (log[u % p] % 4)
    chi2 = lambda u: 0 if u % p == 0 else (-1) ** (log[u % p] % 2)
    S = sum(chi2(x**3 - x) for x in range(p))
    J = sum(chi4(u) * chi2(1 - u) for u in range(p))
    ok1 = abs(S - 2 * J.real) < 1e-9
    ok2 = abs(abs(J)**2 - p) < 1e-6
    ok3 = primary(-J)
    print("p=%d S=%d J=%s  S=2ReJ:%s |J|^2=p:%s -J primary:%s" % (p, S, complex(round(J.real), round(J.imag)), ok1, ok2, ok3))
