---
article_id: af_2cc79d9028cbb9af7f183a15
declaration: theorem
origin: background
---

# Hasse's bound for $C_d$

> **Retired with Route K.** This page described part of Route K, the project's earlier replacement for pole completeness through Tian–Yuan–Zhang and Gross–Zagier. The [main theorem](../../../main/main-theorem.md) no longer uses it. Its Lean declarations were removed (fork issue #77) and are kept at the tag `route-k-final`.

Let $c_d(n)$ be the numbers of [the standard Euler product](l-series.md), $a_n(C_d)$ the
coefficients of $L(C_d,s)$ as in [the coefficients at prime powers](prime-power-coefficients.md),
and $\varphi$ the [Jacobsthal sum](jacobsthal-sums.md) over $\mathbb F_p$.

1. For every natural number $d$ and every prime $p$ with $p\nmid2d$, $c_d(p)=-\varphi(-d^2)$.
2. For every natural number $d$ and every prime $p$, $c_d(p)^2\le4p$.
3. If $d$ is odd and squarefree, then $a_p(C_d)^2\le4p$, that is $|a_p(C_d)|\le2\sqrt p$, for
   every prime $p$.

**Proof sketch.** (1) By [the coefficients for every $d$](coefficients-every-d.md) (4),
$c_d(p)=p+1-N_d(p)$. Over the field $\mathbb F_p$ the [model](cd-model.md) is the curve
$y^2=x^3-d^2x$, and since $p\nmid2d$ its points are its solutions in $\mathbb F_p^2$ and the point at
infinity ([the coefficients at primes](prime-coefficients.md) (3)). As $p\ne2$,
[point counts by the quadratic character](quadratic-character-counts.md) (1) gives
$N_d(p)=p+1+\sum_x\chi(x^3-d^2x)$, and $x^3-d^2x=x\bigl(x^2+(-d^2)\bigr)$, so the sum is
$\varphi(-d^2)$. (2) If $p\mid2d$, then $c_d(p)=0$ by the coefficients for every $d$ (4).
Otherwise $c_d(p)^2=\varphi(-d^2)^2$ by (1); $p\nmid d$ makes $-d^2\ne0$ in $\mathbb F_p$, and
$p\ne2$, so [the Jacobsthal bound](jacobsthal-sums.md) (5) with $q=p$ gives
$\varphi(-d^2)^2\le4p$. (3) By the coefficients for every $d$ (7), $a_p(C_d)=c_d(p)$; apply (2).

## Depends on

- [$L(C_d,s)$ is the Dirichlet series of the standard Euler product](l-series.md)
- [The coefficients of $L(C_d,s)$ at prime powers](prime-power-coefficients.md)
- [Jacobsthal sums over a finite field and their bound](jacobsthal-sums.md)

## Proof depends on

- [The coefficients $c_d(n)$ for every $d$](coefficients-every-d.md)
- [The model $y^2=x^3-d^2x$ over a ring](cd-model.md)
- [The coefficients of $L(C_d,s)$ at primes as point counts](prime-coefficients.md)
- [Point counts by the quadratic character](quadratic-character-counts.md)

## Sources

- [The Hasse bound for the congruent number curves](../../../../sources/rank-locators.md#the-hasse-bound-for-the-congruent-number-curves)
