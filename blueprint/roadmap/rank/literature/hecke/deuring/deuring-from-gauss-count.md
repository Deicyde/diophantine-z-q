---
article_id: af_044722ac04f49508c41fb306
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeFE.deuringCd_of_gaussPointCount
---

# Deuring's identity for $d\equiv1\pmod4$ from Gauss's point count

If [Gauss's point count](../gauss/gauss-point-count.md) holds, then
[Deuring's identity](deuring-identity.md) holds for every squarefree natural number
$d\equiv1\pmod4$.

**Proof sketch.** Such $d$ is odd. The Hecke coefficients have the Euler product for $d$
([the Euler product](../gaussian/hecke-euler-product.md) (2)); Gauss's point count gives Gauss's
theorem at the split primes for $1$, hence for $d$
([the split primes from $y^2=x^3-x$](gauss-split-twist.md) (4), (3)); and
[Deuring's identity from the Euler product](deuring-of-euler-product.md) (3) concludes.

## Depends on

- [Gauss's point count on $y^2=x^3-x$](../gauss/gauss-point-count.md)
- [Deuring's identity for $C_d$](deuring-identity.md)

## Proof depends on

- [The Euler product of $L(\psi_d,s)$](../gaussian/hecke-euler-product.md)
- [The split primes for $C_d$ from the curve $y^2=x^3-x$](gauss-split-twist.md)
- [Deuring's identity from the Euler product and the split primes](deuring-of-euler-product.md)

## Sources

- [Deuring and the Hecke character](../../../../../sources/hecke-locators.md#deuring-and-the-hecke-character)
- [Hecke and Deuring](../../../../../sources/rank-locators.md#hecke-and-deuring)
