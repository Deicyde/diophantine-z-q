---
article_id: af_dd7ab12b0aea4310cae11dda
declaration: def
origin: background
statement: formalized
lean: ZInQ.Contrib.HeckeFE.DeuringCd, ZInQ.Contrib.HeckeFE.cdCoeff_eq_LFunction
---

# Deuring's identity for $C_d$

For natural numbers $d$ and $n$ let $c_d(n)$ be the coefficients of
[the standard Euler product](../../l-function-cd/l-series.md) of $C_d$ and $\lambda_d(n)$ the
[Hecke coefficients](../gaussian/hecke-coefficients.md). *Deuring's identity* holds for $d$ if
$$c_d(n)=\lambda_d(n)\qquad\text{for every }n\ge1.$$
It says that $L(C_d,s)$ and the Hecke L-series $L(\psi_d,s)$ have the same coefficients; it is
proved below for every squarefree $d\equiv1\pmod4$, from Gauss's point count.

If $d$ is odd and squarefree, then $c_d(n)=a_n(C_d)$ for every $n\ge1$, where $a_n(C_d)$ are the
Dirichlet coefficients of $L(C_d,s)$ as in
[the coefficients at prime powers](../../l-function-cd/prime-power-coefficients.md).

**Proof sketch.** Both are the product over $p^k\parallel n$ of the coefficient of $T^k$ in
$P_{d,p}(T)^{-1}$: the first by definition, the second by
[every coefficient](../../l-function-cd/coefficients.md) (2).

## Depends on

- [$L(C_d,s)$ is the Dirichlet series of the standard Euler product](../../l-function-cd/l-series.md)
- [The coefficients of the Hecke L-series $L(\psi_d,s)$](../gaussian/hecke-coefficients.md)
- [The coefficients of $L(C_d,s)$ at prime powers](../../l-function-cd/prime-power-coefficients.md)

## Proof depends on

- [Every coefficient of $L(C_d,s)$](../../l-function-cd/coefficients.md)

## Sources

- [Deuring and the Hecke character](../../../../../sources/hecke-locators.md#deuring-and-the-hecke-character)
- [Hecke and Deuring](../../../../../sources/rank-locators.md#hecke-and-deuring)
