"""Cross-check sel2cong.selmer against PARI's ell2cover (basis of everywhere locally soluble
2-coverings = 2-Selmer group) and ellrank, on 30 squarefree d."""
import sys
import cypari2
from sel2cong import selmer

pari = cypari2.Pari()
pari.allocatemem(10 ** 9)


def oddprimes(n):
    return [int(p) for p in pari.factor(abs(n))[0] if int(p) != 2]


ds = [1, 2, 3, 5, 6, 7, 10, 11, 13, 14, 15, 17, 21, 30, 34, 41, 65, 101, 105, 137, 145, 154,
      210, 219, 345, 386, 1155, 2379, -7, -34]
bad = 0
for d in ds:
    basis, gens = selmer(d, oddprimes(d))
    E = pari.ellinit([0, 0, 0, -d * d, 0])
    cov = pari.ell2cover(E)
    rk = pari.ellrank(E)
    ok = len(basis) == len(cov)
    bad += not ok
    print(d, "mine", len(basis), "ell2cover", len(cov), "ellrank[r,R,s]", rk[0], rk[1], rk[2],
          "OK" if ok else "MISMATCH")
print("mismatches", bad)
