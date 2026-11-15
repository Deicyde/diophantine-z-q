# leaf-audit: sanity case for GrossZagierFormulaCd / GrossConjugationCd at C_5 : y^2 = x^3 - 25x (conductor 800),
# D = -31 (odd fundamental, 2 and 5 split in Q(sqrt -31)). Checks with PARI: root number, L'(C_5,1), L(C_5^D,1),
# so L'(E/K,1) = L'(E,1) L(E^D,1); Heegner point (ellheegner) and its canonical height; Gross conjugation:
# root number -1 => the Heegner point lies in E(Q) up to torsion (sigma y - y torsion).
import cypari2
pari = cypari2.Pari()
pari.allocatemem(2*10**8)
E = pari.ellinit([0, 0, 0, -25, 0])
print("conductor", pari.ellglobalred(E)[0], " root number", pari.ellrootno(E))
D = -31
print("D =", D, " kronecker(D,2) =", pari.kronecker(D, 2), " kronecker(D,5) =", pari.kronecker(D, 5),
      " fundamental:", pari.isfundamental(D))
L1 = pari.ellL1(E, 1)
ED = pari.ellinit(pari.elltwist(E, D))
LD = pari.ellL1(ED, 0)
print("L'(C_5,1) =", L1, "  L(C_5^D,1) =", LD, "  product L'(E/K,1) =", L1 * LD)
P = pari.ellheegner(E)
print("Heegner point (PARI ellheegner) =", P, " canonical height =", pari.ellheight(E, P))
print("analytic rank of C_5^D:", pari.ellanalyticrank(ED)[0])
