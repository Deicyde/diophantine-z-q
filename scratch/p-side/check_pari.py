# Ground-truth sample (30 inputs): compare PARI's a_n(C_5) (n = 1..30) with the facts proved in Lean:
# a_p = -sum_x chi(x^3 - 25x) (p odd, p∤5), a_p = 0 for p ≡ 3 mod 4 or p | 10, a_n^2 <= sigma0(n)^2 n.
import cypari2
pari = cypari2.Pari()
d = 5
E = pari.ellinit([0, 0, 0, -d * d, 0])
an = pari.ellan(E, 30)
ok = True
for n in range(1, 31):
    a = int(an[n - 1])
    s0 = int(pari.numdiv(n))
    if a * a > s0 * s0 * n:
        ok = False; print("bound fails", n, a)
    if pari.isprime(n):
        p = n
        if p % 4 == 3 or (2 * d) % p == 0:
            if a != 0: ok = False; print("a_p != 0", p, a)
        if (2 * d) % p != 0:
            cs = sum(int(pari.kronecker(x ** 3 - d * d * x, p)) for x in range(p))
            if a != -cs: ok = False; print("charsum mismatch", p, a, cs)
print("a_n(C_5), n=1..30:", [int(x) for x in an])
print("all checks pass:", ok)
