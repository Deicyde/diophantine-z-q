"""Numerical values of calL(n)^2 = L(E_n,1) / (2^{2k-2-a} Omega_{n,inf}) for small n (TYZ L338-353),
to check calL(1) = 1 and the normalisation of TYZ Lemma 2.8 at m = 3 (where w_K = 3)."""
import cypari2
pari = cypari2.Pari()
I = pari('intnum(x=[1,-1/2],[oo,-3/2], 1/sqrt(x^3-x))')
for n, k in ((1, 0), (3, 1), (11, 1), (19, 1), (33, 2)):
    E = pari.ellinit([0, 0, 0, -n * n, 0])
    L1 = pari.lfun(pari.lfuncreate(E), 1)
    Om = 2 / pari.sqrt(n) * I
    val = L1 / (pari(2) ** (2 * k - 2 - 1) * Om)
    print(f"n={n}: calL(n)^2 = {float(val):.10f}")
