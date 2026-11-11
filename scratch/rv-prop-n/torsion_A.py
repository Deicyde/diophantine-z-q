# I4 / Lemma 3.16 sanity: A: 2y^2 = x^3 + x  ~  Y^2 = X^3 + 4X (X=2x, Y=4y).
import cypari2
pari = cypari2.Pari()
E = pari('ellinit([0,0,0,4,0])')
print("conductor", pari.ellglobalred(E)[0], "tors/Q", pari.elltors(E)[:2])
for pol in ['y^2+1', 'y^2-2', 'y^2+2', 'y^4+1', 'y^4-2*y^2+9']:
    K = pari.nfinit(pol)
    EK = pari.ellinit([0,0,0,4,0], K)
    print(pol, "tors", pari.elltors(EK)[:2])
