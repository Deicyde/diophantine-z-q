---
article_id: af_93054c0fe96ab22d043f6d86
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Progressions.norm_deriv_LFunction_le, ZInQ.Progressions.deriv_LFunction_eq
---

# A bound for $L'(\sigma,\chi)$ to the right of $1$

Let $q\ge1$, let $\chi$ be a nonprincipal Dirichlet character modulo $q$, and put
$M=\log q+3$. For every real $\sigma>1$, the complex derivative of the $L$-function
satisfies
$$|L'(\sigma,\chi)|\le M^2 ,$$
and $L'(\sigma,\chi)=-\sum_{n\ge1}\chi(n)\log n\cdot n^{-\sigma}$.

**Proof sketch.** For $\sigma>1$ the series may be differentiated term by term, which gives
the formula for $L'(\sigma,\chi)$. Since $\chi$ is nonprincipal, $q\ge2$. Split the series at
$N=q$: the terms with $n\le q$ contribute at most $\sum_{n\le q}\log n/n\le\log q\,(1+\log q)$,
and by the tail bound the rest has absolute value at most
$q\log(q+1)(q+1)^{-\sigma}\le\log q+1$. The total is at most
$\log^2q+2\log q+1\le(\log q+3)^2$.

## Depends on

None.

## Proof depends on

- [Tails of the twisted harmonic sums](tails.md)

## Sources

- [Apostol, Chapter 11](../../../sources/progressions-locators.md#apostol-chapter-11)
- [Apostol, Chapter 6](../../../sources/progressions-locators.md#apostol-chapter-6)
