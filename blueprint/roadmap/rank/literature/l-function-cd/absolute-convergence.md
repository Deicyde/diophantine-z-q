---
article_id: af_36f98bb18398d8fc2566c44d
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.PSide.convolution_one_one, ZInQ.Contrib.PSide.LSeriesSummable_cdCoeff, ZInQ.Contrib.PSide.LSeriesSummable_cd, ZInQ.Contrib.PSide.abscissaOfAbsConv_cd_le, ZInQ.Contrib.PSide.differentiableOn_LSeries_cd
---

# $L(C_d,s)$ converges absolutely on $\operatorname{Re}s>3/2$

Let $c_d(n)$ be the numbers of [the standard Euler product](l-series.md), $a_n(C_d)$ the
coefficients of $L(C_d,s)$ as in [the coefficients at prime powers](prime-power-coefficients.md),
and $\sigma_0(n)$ the number of divisors of $n$, with $\sigma_0(0)=0$.

1. For every $n$, the Dirichlet convolution of the constant function $1$ with itself takes the
   value $\sigma_0(n)$ at $n$.
2. For every natural number $d$ and every complex number $s$ with $\operatorname{Re}s>3/2$, the
   series $\sum_{n\ge1}c_d(n)\,n^{-s}$ converges absolutely.
3. If $d$ is odd and squarefree, then $\sum_{n\ge1}a_n(C_d)\,n^{-s}$ converges absolutely for every
   complex $s$ with $\operatorname{Re}s>3/2$.
4. If $d$ is odd and squarefree, the abscissa of absolute convergence of
   $\sum_{n\ge1}a_n(C_d)\,n^{-s}$ is at most $3/2$.
5. If $d$ is odd and squarefree, then $L(C_d,s)$, read as in
   [entire continuations](../l-series-continuation.md), is complex differentiable on the half-plane
   $\operatorname{Re}s>3/2$.

So for odd squarefree $d$ an entire continuation of $L(C_d,s)$ is required to agree, on
$\operatorname{Re}s>3/2$, with the sum of an absolutely convergent series. This article does not show
that an entire continuation exists; [Hecke's continuation holds](../hecke/hecke-continuation-holds.md)
proves that, for every $d\ne0$.

**Proof sketch.** (1) The value at $n$ counts the pairs $(a,b)$ with $ab=n$, one for each divisor
$a$ of $n$; at $n=0$ both sides are $0$. (2) Put $s'=s-1/2$, so $\operatorname{Re}s'>1$. The
Dirichlet series of the constant function $1$ converges absolutely at $s'$, and the Dirichlet
convolution of two series converging absolutely at $s'$ converges absolutely at $s'$; by (1),
$\sum_n\sigma_0(n)\,n^{-\operatorname{Re}s'}$ converges. By
[the bounds for the coefficients](coefficient-bounds.md) (3), $|c_d(n)|\le\sigma_0(n)\sqrt n$, so
$|c_d(n)\,n^{-s}|\le\sigma_0(n)\,n^{-(\operatorname{Re}s-1/2)}$ for $n\ge1$; compare. (3) By
[the coefficients for every $d$](coefficients-every-d.md) (7), $a_n(C_d)=c_d(n)$; apply (2).
(4) By (3), the series converges absolutely at every real $y>3/2$. (5) A Dirichlet series is
complex differentiable on the open half-plane to the right of its abscissa of absolute
convergence, and by (4) that half-plane contains $\operatorname{Re}s>3/2$.

## Depends on

- [$L(C_d,s)$ is the Dirichlet series of the standard Euler product](l-series.md)
- [The coefficients of $L(C_d,s)$ at prime powers](prime-power-coefficients.md)
- [Entire continuations of the L-series of an elliptic curve](../l-series-continuation.md)

## Proof depends on

- [Bounds for the coefficients $c_d(n)$](coefficient-bounds.md)
- [The coefficients $c_d(n)$ for every $d$](coefficients-every-d.md)

## Sources

- [The L-series of an elliptic curve](../../../../sources/rank-locators.md#the-l-series-of-an-elliptic-curve)
- [The Hasse bound for the congruent number curves](../../../../sources/rank-locators.md#the-hasse-bound-for-the-congruent-number-curves)
