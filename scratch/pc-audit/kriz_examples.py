"""Conductors, f_0 (= sqrt of prime-to-2 part of the conductor), ranks, analytic ranks and
2-Selmer dimensions for small congruent number curves C_d and Kriz's example 256b1."""
import cypari2
pari = cypari2.Pari(); pari.allocatemem(10 ** 9)
def info(name, ai):
    E = pari.ellinit(ai)
    N = int(pari.ellglobalred(E)[0])
    odd = N
    while odd % 2 == 0:
        odd //= 2
    f0 = int(pari.sqrtint(odd))
    assert f0 * f0 == odd
    ar = pari.ellanalyticrank(E)
    rk = pari.ellrank(E)
    s2 = len(pari.ell2cover(E))
    print(f"{name}: conductor {N} = 2^{pari.valuation(N,2)}*{odd}, f0 = {f0}, analytic rank {int(ar[0])} "
          f"(L^(r)(1)/r! ~ {float(ar[1]):.6f}), ellrank [r,R] = [{int(rk[0])},{int(rk[1])}], "
          f"dim Sel2 = {s2} (ell2cover basis size), points {rk[3]}")
info("256b1 y^2=x^3-2x", [0, 0, 0, -2, 0])
for d in [1, 2, 3, 5, 6, 7, 10, 11, 13]:
    info(f"C_{d}", [0, 0, 0, -d * d, 0])
