---
article_id: af_3c6bc01ddd53f4415bff2bb4
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeFE.cdCoeff_prime_eq, ZInQ.Contrib.HeckeFE.deuringCd_of_heckeEuler, ZInQ.Contrib.HeckeFE.GaussSplit, ZInQ.Contrib.HeckeFE.deuringCd_of_heckeEuler_gaussSplit
---

# Deuring's identity from the Euler product and the split primes

Let $c_d(n)$ be the coefficients of [the standard Euler product](../../l-function-cd/l-series.md)
with [Euler polynomials](../../l-function-cd/cd-euler-polynomial.md) $P_{d,p}$, and $\lambda_d(n)$
the [Hecke coefficients](../gaussian/hecke-coefficients.md). *Gauss's theorem at the split primes*
holds for $d$ if $c_d(p)=\lambda_d(p)$ for every prime $p\equiv1\pmod4$ with $p\nmid d$.

1. If $d$ is odd and squarefree and $p$ is a prime with $p\nmid2d$, then $c_d(p)=p+1-N_d(p)$, where
   $N_d(p)$ is the number of points of the model $y^2=x^3-d^2x$ over $\mathbb Z/p\mathbb Z$, the
   point at infinity included.
2. If $d$ is odd and squarefree, the Hecke coefficients have the
   [Euler product](../gaussian/hecke-euler-product.md) for $d$, and $c_d(p)=\lambda_d(p)$ for every
   prime $p$, then [Deuring's identity](deuring-identity.md) holds for $d$.
3. If $d$ is odd and squarefree, the Hecke coefficients have the Euler product for $d$, and Gauss's
   theorem at the split primes holds for $d$, then Deuring's identity holds for $d$.

**Proof sketch.** (1) [Deuring's identity for $C_d$](deuring-identity.md) identifies $c_d(p)$ with
the Dirichlet coefficient $a_p(C_d)$, which
[the coefficients at primes](../../l-function-cd/prime-coefficients.md) computes for $p\nmid2d$.

(2) Both sides of Deuring's identity at $n\ge1$ are products over $p^k\parallel n$, of the
coefficients of $T^k$ in $P_{d,p}(T)^{-1}$ and in $H_{d,p}(T)^{-1}$ respectively. The Hecke Euler
polynomial $H_{d,p}$ is $P_{d,p}$ with its coefficients read in $\mathbb C$: both are $1$ at
$p\mid2d$, and at $p\nmid2d$ the middle coefficient $-\lambda_d(p)=-c_d(p)=-(p+1-N_d(p))$ by the
hypothesis and (1). Reading the coefficients in $\mathbb C$ commutes with inversion
([quadratic power series](../gaussian/quadratic-power-series.md) (2)).

(3) The hypothesis of (2) at every prime $p$: if $p\mid d$, by
[the small primes](deuring-small-primes.md) (5); if $p=2$, by the small primes (6); if
$p\equiv1\pmod4$ and $p\nmid d$, by Gauss's theorem at the split primes; if $p\equiv3\pmod4$ and
$p\nmid d$, by the small primes (4).

## Depends on

- [$L(C_d,s)$ is the Dirichlet series of the standard Euler product](../../l-function-cd/l-series.md)
- [The Euler polynomial of $C_d$ at $p$](../../l-function-cd/cd-euler-polynomial.md)
- [The coefficients of the Hecke L-series $L(\psi_d,s)$](../gaussian/hecke-coefficients.md)
- [The Euler product of $L(\psi_d,s)$](../gaussian/hecke-euler-product.md)
- [Deuring's identity for $C_d$](deuring-identity.md)

## Proof depends on

- [The coefficients of $L(C_d,s)$ at primes as point counts](../../l-function-cd/prime-coefficients.md)
- [Inverses of quadratic power series](../gaussian/quadratic-power-series.md)
- [Deuring's identity at the primes $2$, $p\mid d$ and $p\equiv3\pmod4$](deuring-small-primes.md)

## Sources

- [Deuring and the Hecke character](../../../../../sources/hecke-locators.md#deuring-and-the-hecke-character)
