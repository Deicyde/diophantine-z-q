# Check (PARI): for E_j = Mathlib ofJNe0Or1728 j = [j-1728, 0, 0, -36(j-1728)^3, -(j-1728)^5],
# the primitive N-division polynomial in x (x-coordinates of points of exact order N) has
# discriminant (in x) supported on j, j-1728 up to a rational constant, and is irreducible
# over Q(j) of degree (N^2-1)/2 (N odd prime) / as listed. Supports T2 for E_j and the degree bound.
import cypari2
pari = cypari2.Pari()
pari.allocatemem(2*10**9)
E = pari('ellinit([j-1728, 0, 0, -36*(j-1728)^3, -(j-1728)^5])')
print("disc E =", pari.factor(E[11]))  # E.disc
for N in [2, 3, 4, 5, 6, 7]:
    psi = pari.elldivpol(E, N, 'x')
    # remove contributions of proper divisors d | N, d < N
    f = psi
    for d in range(1, N):
        if N % d == 0 and d > 1:
            g = pari.elldivpol(E, d, 'x')
            while pari.poldegree(pari.gcd(f, g), 'x') > 0:
                f = f / pari.gcd(f, g)
    f = pari.numerator(f) if False else f
    fac = pari.factor(f)
    degs = [int(pari.poldegree(fac[0][i], 'x')) for i in range(len(fac[0]))]
    disc = pari.poldisc(f, 'x')
    print(N, "deg", int(pari.poldegree(f, 'x')), "factor degs over Q(j)[x]", degs,
          "disc support:", pari.factor(disc)[0])
