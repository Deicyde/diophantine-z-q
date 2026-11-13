---
article_id: af_79d59a7e53f0730039078aa3
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeAll.LFunction_cd_apply_prime_pow', ZInQ.Contrib.HeckeAll.LFunction_cd_apply_prime', ZInQ.Contrib.HeckeAll.LFunction_cd_apply', ZInQ.Contrib.HeckeAll.LFunction_cd_apply_prime_eq_sub_card', ZInQ.Contrib.HeckeAll.LFunction_cd_apply_prime_of_dvd', ZInQ.Contrib.HeckeAll.LSeries_cd_eq'
---

# $L(C_d,s)$ for every squarefree $d$

Let $d$ be squarefree, odd or even; $a_n(C_d)$ are the Dirichlet coefficients of $L(C_d,s)$ as in
[the coefficients at prime powers](../../l-function-cd/prime-power-coefficients.md), $P_{d,p}$ is
[the Euler polynomial](../../l-function-cd/cd-euler-polynomial.md), and $c_d(n)$ are the
coefficients of [the standard Euler product](../../l-function-cd/l-series.md).

1. For every prime $p$ and $k\ge0$, $a_{p^k}(C_d)$ is the coefficient of $T^k$ in $P_{d,p}(T)^{-1}$.
2. For every prime $p$, $a_p(C_d)=0$ if $p\mid2d$, and $a_p(C_d)=p+1-N_d(p)$ otherwise, where
   $N_d(p)$ is the number of points of $y^2=x^3-d^2x$ over $\mathbb Z/p\mathbb Z$, the point at
   infinity included.
3. For every $n\ge1$, $a_n(C_d)=\prod_{p^k\parallel n}[T^k]\,P_{d,p}(T)^{-1}$.
4. For every prime $p\nmid2d$,
   $a_p(C_d)=p-\#\{(x,y)\in\mathbb F_p^2:y^2=x^3-d^2x\}$; for every prime $p\mid2d$, $a_p(C_d)=0$.
5. For every complex number $s$, $L(C_d,s)=\sum_{n\ge1}c_d(n)n^{-s}$, both sides read as sums where
   the series converge absolutely and $0$ elsewhere.

These are the statements of [the computation of $L(C_d,s)$](../../l-function-cd/README.md) with the
hypothesis that $d$ is odd removed.

**Proof sketch.** (1) As in [the coefficients at prime powers](../../l-function-cd/prime-power-coefficients.md),
with the local polynomial at the place over $p$ given by
[the local factors for every squarefree $d$](cd-local-every-squarefree.md) (3).

(2) The case $k=1$ of (1): the coefficient of $T$ in $P_{d,p}(T)^{-1}$ is minus the coefficient of
$T$ in $P_{d,p}$.

(3) $a_n(C_d)$ is multiplicative ([every coefficient](../../l-function-cd/coefficients.md) (1));
apply (1) at each prime power.

(4) By (2) and the count of points of $y^2=x^3-d^2x$ over $\mathbb F_p$ for $p\nmid2d$
([the coefficients at primes](../../l-function-cd/prime-coefficients.md)).

(5) The two Dirichlet series have the same coefficients at every $n\ge1$ by (3).

## Depends on

- [The coefficients of $L(C_d,s)$ at prime powers](../../l-function-cd/prime-power-coefficients.md)
- [The Euler polynomial of $C_d$ at $p$](../../l-function-cd/cd-euler-polynomial.md)
- [$L(C_d,s)$ is the Dirichlet series of the standard Euler product](../../l-function-cd/l-series.md)

## Proof depends on

- [The local factors of $C_d$ for every squarefree $d$](cd-local-every-squarefree.md)
- [Every coefficient of $L(C_d,s)$](../../l-function-cd/coefficients.md)
- [The coefficients of $L(C_d,s)$ at primes as point counts](../../l-function-cd/prime-coefficients.md)

## Sources

- [The curves for even and non-squarefree d](../../../../../sources/hecke-locators.md#the-curves-for-even-and-non-squarefree-d)
- [The L-series of the congruent number curves](../../../../../sources/rank-locators.md#the-l-series-of-the-congruent-number-curves)
