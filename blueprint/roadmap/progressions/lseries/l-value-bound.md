---
article_id: af_00cb29ee2a96209295abbc9f
declaration: theorem
origin: background
---

# A bound for $L(\sigma,\chi)$ near $1$

Let $q\ge1$, let $\chi$ be a nonprincipal Dirichlet character modulo $q$, and let $L(s,\chi)$
be its $L$-function, the entire continuation of $\sum_{n\ge1}\chi(n)n^{-s}$. Put
$M=\log q+3$. For every real $\sigma$ with $1\le\sigma\le2$,
$$|L(\sigma,\chi)|\le M .$$

**Proof sketch.** For $\sigma>1$ the series converges absolutely to $L(\sigma,\chi)$. Split it
at $N=q$: the first $q$ terms contribute at most $\sum_{n\le q}1/n\le1+\log q$, and by the
tail bound every partial sum $\sum_{q<n\le K}\chi(n)n^{-\sigma}$ has absolute value at most
$2q/q=2$, so $|L(\sigma,\chi)|\le\log q+3$. (Summation by parts gives the sharper
$q(q+1)^{-\sigma}\le1$ for the tail.) The value at $\sigma=1$ follows by continuity of
$L(s,\chi)$ as $\sigma\to1^+$.

## Depends on

None.

## Proof depends on

- [Character sums are bounded by the modulus](character-sums.md)
- [Tails of the twisted harmonic sums](tails.md)

## Sources

- [Apostol, Chapter 6](../../../sources/progressions-locators.md#apostol-chapter-6)
- [Apostol, Chapter 3](../../../sources/progressions-locators.md#apostol-chapter-3)
