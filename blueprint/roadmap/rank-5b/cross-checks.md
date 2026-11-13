---
article_id: af_0266aad120a8752a17676e84
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.det_M5b_21, ZInQ.RouteK.Rank5b.det_M5b_5, ZInQ.RouteK.Rank5b.Config.M5bc_of_iso, ZInQ.RouteK.Rank5b.Config.det_M5bc_of_iso, ZInQ.RouteK.Rank5b.primeFactors_21, ZInQ.RouteK.Rank5b.legBit_3_7, ZInQ.RouteK.Rank5b.legBit_7_3, ZInQ.RouteK.Rank5b.enum21, ZInQ.RouteK.Rank5b.enum21_inj, ZInQ.RouteK.Rank5b.enum21_prime, ZInQ.RouteK.Rank5b.enum21_mem, ZInQ.RouteK.Rank5b.equiv21, ZInQ.RouteK.Rank5b.idx5, ZInQ.RouteK.Rank5b.M5bc_primeCfg_21, ZInQ.RouteK.Rank5b.primeFactors_5
---

# Two values of the row-5b determinant

For $n=21=3\cdot7$, $\det M_{5b}=1$; for $n=5$, $\det M_{5b}=0$.

For $n=21$ this agrees with Corollary 4.4: by the note's computations, which are not part of
this statement, $C_{21}$ has a Selmer group with $8$ elements and $7$ is a first coordinate.

**Proof sketch.** The determinant is unchanged when the primes are relabelled. For $21$, with
the primes listed as $(3,7)$, the bits are $(7/3)_+=0$ and $(3/7)_+=1$, $y_3=y_7=1$, $z_3=1$,
$z_7=0$, and the $5\times5$ determinant over $\mathbb F_2$ is expanded along rows, a finite
computation. For $5$, $y_5=0$, so the bordering row of $M_{5b}$ vanishes.

## Depends on

- [Smith's matrices $L$, $M_1$ and $M_{5b}$](smith-matrices.md)

## Sources

- [Validation](../../sources/rank-5b-locators.md#validation)
