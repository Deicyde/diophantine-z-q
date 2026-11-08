---
article_id: af_00cb29ee2a96209295abbc9f
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Progressions.norm_LFunction_le, ZInQ.Progressions.norm_LFunction_le_of_one_lt, ZInQ.Progressions.norm_LFunction_one_le, ZInQ.Progressions.sum_norm_char_div_cpow_le, ZInQ.Progressions.LFunction_one_le_of_forall_one_lt
---

# A bound for $L(\sigma,\chi)$ near $1$

Let $q\ge1$, let $\chi$ be a nonprincipal Dirichlet character modulo $q$, and let $L(s,\chi)$
be its $L$-function, the entire continuation of $\sum_{n\ge1}\chi(n)n^{-s}$. Put
$M=\log q+3$. For every real $\sigma\ge1$,
$$|L(\sigma,\chi)|\le M ;$$
in particular $|L(1,\chi)|\le M$.

**Proof sketch.** For $\sigma>1$ the series converges absolutely to $L(\sigma,\chi)$. Split it
at $N=q$: the first $q$ terms contribute at most $\sum_{n\le q}1/n\le1+\log q$, and by the
tail bound the rest has absolute value at most $q(q+1)^{-\sigma}\le1$, so
$|L(\sigma,\chi)|\le\log q+3$. The value at $\sigma=1$ follows by continuity of $L(s,\chi)$ as
$\sigma\to1^+$: a closed bound on $L(\sigma,\chi)$ for all $\sigma>1$ passes to $\sigma=1$.

## Depends on

None.

## Proof depends on

- [Character sums are bounded by the modulus](character-sums.md)
- [Tails of the twisted harmonic sums](tails.md)

## Sources

- [Apostol, Chapter 6](../../../sources/progressions-locators.md#apostol-chapter-6)
- [Apostol, Chapter 3](../../../sources/progressions-locators.md#apostol-chapter-3)
