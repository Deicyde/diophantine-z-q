---
article_id: af_8b98924559f296a33e4f932f
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Contrib.HeckeFE.GaussPointCount
---

# Gauss's point count on $y^2=x^3-x$

*Gauss's point count* is the following assertion. For every prime $p\equiv1\pmod4$,
$$p-\#\{(x,y)\in\mathbb F_p^2:y^2=x^3-x\}=\frac14\sum_{\alpha\in A_p}u(\alpha)\,\alpha,$$
where $A_p$ is the set of [Gaussian integers of norm $p$](../gaussian/norm-fibres.md) and $u$ the
[primary unit](../gaussian/primary-unit.md). The left side is the coefficient $c_1(p)$ of
$L(C_1,s)$, and the right side is the [Hecke coefficient](../gaussian/hecke-coefficients.md)
$\lambda_1(p)$. It is [proved](gauss-point-count-holds.md).

## Depends on

- [Gaussian integers as pairs, norms and units](../gaussian/norm-fibres.md)
- [The primary unit of a Gaussian integer modulo 4](../gaussian/primary-unit.md)

## Sources

- [The point count of Gauss](../../../../../sources/hecke-locators.md#the-point-count-of-gauss)
