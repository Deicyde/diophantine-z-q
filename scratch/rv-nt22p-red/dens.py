"""Independent count of good slope primes (GoodSlopePrime, via ellcard) below 2e5."""
from ap_search import good_slope_prime
import cypari2
pari = cypari2.Pari()
P = [int(p) for p in pari("primes([3,200000])")]
g = [p for p in P if good_slope_prime(p)]
print("primes < 2e5 (odd):", len(P), " good:", len(g), " share:", len(g) / (len(P) + 1))
cls = [p for p in P if p % 8 == 1 and int(pari(f"kronecker(7,{p})")) == -1]
print("class p=1 (8), (7/p)=-1:", len(cls), " good in class:", sum(1 for p in g if p in set(cls)), " all good in class:", set(g) <= set(cls) | {p for p in g if p < 325})
