---
article_id: af_cc2963c1238dffe3bb9ca9b6
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Progressions.norm_sum_div_sub_LFunction_one_le, ZInQ.Progressions.norm_partialSum_sub_LFunction_one_le, ZInQ.Progressions.norm_partialSum_sub_LFunction_one_le', ZInQ.Progressions.continuous_sum_char_div_cpow
---

# Partial sums of $\chi(n)/n$ approximate $L(1,\chi)$

Let $q\ge1$ and let $\chi$ be a nonprincipal Dirichlet character modulo $q$. For every integer
$N\ge0$,
$$\Bigl|\sum_{1\le n\le N}\frac{\chi(n)}{n}-L(1,\chi)\Bigr|\le\frac{q}{N+1},$$
and hence, for every real $x>0$,
$$\Bigl|\sum_{1\le n\le x}\frac{\chi(n)}{n}-L(1,\chi)\Bigr|\le\frac{2q}{x}.$$

**Proof sketch.** For real $\sigma>1$ the series for $L(\sigma,\chi)$ converges absolutely,
and by the tail bound
$|L(\sigma,\chi)-\sum_{n\le N}\chi(n)n^{-\sigma}|\le q(N+1)^{-\sigma}\le q/(N+1)$. Let
$\sigma\to1^+$: the left side tends to $|L(1,\chi)-\sum_{n\le N}\chi(n)/n|$ by continuity of
$L(s,\chi)$ and of each term, so this is at most $q/(N+1)$. The value at $1$ is reached as a
limit; no conditionally convergent series is summed. For $x\ge1$ take $N=\lfloor x\rfloor$,
so $q/(N+1)\le q/x\le2q/x$. For $0<x<1$ the sum is empty and
$|L(1,\chi)|\le q\le2q/x$, the case $N=0$.

## Depends on

None.

## Proof depends on

- [Character sums are bounded by the modulus](character-sums.md)
- [Tails of the twisted harmonic sums](tails.md)

## Sources

- [Apostol, Chapter 6](../../../sources/progressions-locators.md#apostol-chapter-6)
