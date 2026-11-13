---
article_id: af_80b1706d933142637d725534
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeFE.literature_hecke_fe_of_mult_split_gaussPointCount, ZInQ.Contrib.HeckeFE.literature_hecke_fe_of_gaussPointCount
---

# Hecke's continuation for $d\equiv5\pmod8$ and the functional equation from Gauss's point count

1. Suppose that, for every squarefree $d\equiv5\pmod8$, the Hecke coefficients are
   [multiplicative](gaussian/hecke-multiplicative.md) and
   [the Hecke relation at the split primes](gaussian/hecke-split-recursion.md) holds for $d$, and
   that [Gauss's point count](gauss/gauss-point-count.md) holds. Then
   [Hecke's continuation for $d\equiv5\pmod8$](continuation-of-deuring.md) and
   [the functional equation on the critical strip](../functional-equation.md) both hold.
2. If Gauss's point count holds, then Hecke's continuation for $d\equiv5\pmod8$ and the functional
   equation on the critical strip both hold.

**Proof sketch.** (1) Let $d\equiv5\pmod8$ be squarefree; it is odd and $d\equiv1\pmod4$.

*Deuring's identity for $d$.* The Hecke relation extends from the split primes to all primes
([the Hecke relation](gaussian/hecke-split-recursion.md) (2)), so with multiplicativity the Hecke
coefficients have [the Euler product](gaussian/hecke-euler-product.md) for $d$ (its (1)). Gauss's
point count gives Gauss's theorem at the split primes for $1$, hence for $d$
([the split primes from $y^2=x^3-x$](deuring/gauss-split-twist.md) (4), (3)). So Deuring's identity
holds for $d$ ([from the Euler product](deuring/deuring-of-euler-product.md) (3)).

*The Fourier identity for $d$.* The odd Gauss sum identity holds at every odd prime, hence for $d$
([the odd part](fourier/odd-gauss-sum.md) (1), (4)), and so the Fourier identity holds for $d$
([the Fourier identity](fourier/fourier-identity.md)).

Then [the continuation from Deuring's identity](continuation-of-deuring.md) (2) gives Hecke's
continuation for $d\equiv5\pmod8$, and
[the functional equation from Deuring's identity](functional-equation-of-deuring.md) (5) gives the
functional equation.

(2) Multiplicativity holds for every $d$ ([multiplicativity](gaussian/hecke-multiplicative.md)) and
so does the Hecke relation at the split primes ([the Hecke relation](gaussian/hecke-split-recursion.md)
(1)); apply (1).

## Depends on

- [The Hecke coefficients are multiplicative](gaussian/hecke-multiplicative.md)
- [The Hecke relation at prime powers](gaussian/hecke-split-recursion.md)
- [Gauss's point count on $y^2=x^3-x$](gauss/gauss-point-count.md)
- [The continuation of $L(C_d,s)$ from Deuring's identity](continuation-of-deuring.md)
- [The functional equation of $L(C_d,s)$ on the strip $0<\operatorname{Re}s<2$](../functional-equation.md)

## Proof depends on

- [The Euler product of $L(\psi_d,s)$](gaussian/hecke-euler-product.md)
- [The split primes for $C_d$ from the curve $y^2=x^3-x$](deuring/gauss-split-twist.md)
- [Deuring's identity from the Euler product and the split primes](deuring/deuring-of-euler-product.md)
- [The odd part of the Fourier transform](fourier/odd-gauss-sum.md)
- [The Fourier identity for $\omega_d$](fourier/fourier-identity.md)
- [The functional equation from Deuring's identity and the Fourier identity](functional-equation-of-deuring.md)

## Sources

- [The Hecke section](../../../../sources/hecke-locators.md#the-hecke-section)
- [Hecke and Deuring](../../../../sources/rank-locators.md#hecke-and-deuring)
