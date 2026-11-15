"""h29-fix: TYZ's L(n)^2 = L(E_n,1)/(2^{2k(n)-2-a(n)} Omega_{n,inf}) (TYZ L336-353) at n = 1, 3, 11, 19, 17, 41.
Omega_{n,inf} = (2/sqrt n) * int_1^oo dx/sqrt(x^3-x). PARI/GP via cypari2."""
import cypari2
pari = cypari2.Pari()
pari.set_real_precision(40)
I = pari('intnum(x=[1,-1/2],[oo,-3/2], 1/sqrt(x^3-x))')
for n in [1, 3, 11, 19, 17, 41]:
    E = pari.ellinit([0, 0, 0, -n*n, 0])
    L1 = pari.lfun(E, 1)
    k = len([p for p in pari.factor(n)[0] if p != 2]) if n > 1 else 0
    a = 1 if n % 2 else 0
    Om = 2 / pari.sqrt(n) * I
    val = L1 / (pari(2) ** (2*k - 2 - a) * Om)
    print(n, "k=%d" % k, "L(n)^2 =", pari.round(val, 1)[0] if False else val)
