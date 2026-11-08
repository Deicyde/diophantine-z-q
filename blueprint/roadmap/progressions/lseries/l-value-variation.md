---
article_id: af_a3dd016a0e9c90e1e4566039
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Progressions.norm_LFunction_sub_one_le, ZInQ.Progressions.continuous_LFunction_ofReal
---

# Variation of $L(\sigma,\chi)$ near $1$

Let $q\ge1$, let $\chi$ be a nonprincipal Dirichlet character modulo $q$, and put
$M=\log q+3$. For every real $\sigma\ge1$,
$$|L(\sigma,\chi)-L(1,\chi)|\le(\sigma-1)M^2 .$$

**Proof sketch.** The function $t\mapsto L(t,\chi)$ on $[1,\sigma]$ is the restriction of an
entire function, so it is continuous on $[1,\sigma]$ and differentiable with derivative
$L'(t,\chi)$, of absolute value at most $M^2$ for $1<t\le\sigma$. The mean value inequality
for vector-valued functions on a segment, which allows one exceptional endpoint, gives the
bound.

## Depends on

None.

## Proof depends on

- [A bound for $L'(\sigma,\chi)$ to the right of $1$](derivative-bound.md)

## Sources

- [Apostol, Chapter 6](../../../sources/progressions-locators.md#apostol-chapter-6)
