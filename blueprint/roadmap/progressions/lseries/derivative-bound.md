---
article_id: af_93054c0fe96ab22d043f6d86
declaration: theorem
origin: background
---

# A bound for $L'(\sigma,\chi)$ near $1$

Let $q\ge1$, let $\chi$ be a nonprincipal Dirichlet character modulo $q$, and put
$M=\log q+3$. For every real $\sigma$ with $1\le\sigma\le2$, the complex derivative of the
$L$-function satisfies
$$|L'(\sigma,\chi)|\le M^2 .$$

**Proof sketch.** For $\sigma>1$ the series may be differentiated term by term:
$L'(\sigma,\chi)=-\sum_{n\ge1}\chi(n)\log n\cdot n^{-\sigma}$, the limit of the partial
sums, each of which has absolute value at most $M^2$ by the bound on partial sums of
$\chi(n)\log n/n^{\sigma}$. The derivative of the entire function $L(s,\chi)$ is continuous,
which gives $\sigma=1$.

## Depends on

None.

## Proof depends on

- [Partial sums of $\chi(n)\log n/n$](log-partial-sums.md)

## Sources

- [Apostol, Chapter 11](../../../sources/progressions-locators.md#apostol-chapter-11)
- [Apostol, Chapter 6](../../../sources/progressions-locators.md#apostol-chapter-6)
