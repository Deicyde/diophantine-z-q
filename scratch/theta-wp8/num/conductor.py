# Conductor of C_d : y^2 = x^3 - d^2 x for d = 5 (mod 8) squarefree (PARI ellglobalred).
import cypari2
pari = cypari2.Pari()
for d in [5, 13, 21, 29, 37, 53]:
    E = pari.ellinit([0, 0, 0, -d*d, 0])
    N = pari.ellglobalred(E)[0]
    print(d, N, N == 32*d*d)
# a_p(C_d) = (d/p) a_p(C_1): no level-32 newform has the coefficients of C_d, d = 5 (mod 8)
E1 = pari.ellinit([0, 0, 0, -1, 0])
for d in [5, 13]:
    Ed = pari.ellinit([0, 0, 0, -d*d, 0])
    p = next(p for p in pari.primes(50) if p % 4 == 1 and pari.kronecker(d, p) == -1 and p != d)
    print('d', d, 'p', p, 'a_p(C_1)', pari.ellap(E1, p), 'a_p(C_d)', pari.ellap(Ed, p))
