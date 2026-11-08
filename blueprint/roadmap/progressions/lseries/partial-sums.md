---
article_id: af_cc2963c1238dffe3bb9ca9b6
declaration: theorem
origin: background
---

# Partial sums of $\chi(n)/n$ approximate $L(1,\chi)$

Let $q\ge1$ and let $\chi$ be a nonprincipal Dirichlet character modulo $q$. For every real
$x\ge1$,
$$\Bigl|\sum_{1\le n\le x}\frac{\chi(n)}{n}-L(1,\chi)\Bigr|\le\frac{2q}{x}.$$

**Proof sketch.** Let $N=\lfloor x\rfloor$. For real $\sigma>1$ the series for
$L(\sigma,\chi)$ converges absolutely, and summation by parts against the character sum
bound gives $|L(\sigma,\chi)-\sum_{n\le N}\chi(n)n^{-\sigma}|\le q(N+1)^{-\sigma}$. Let
$\sigma\to1^+$: the left side tends to $|L(1,\chi)-\sum_{n\le N}\chi(n)/n|$ by continuity of
$L(s,\chi)$ and of each term, so this is at most $q/(N+1)\le q/x\le2q/x$. The value at $1$
is reached as a limit; no conditionally convergent series is summed.

## Depends on

None.

## Proof depends on

- [Character sums are bounded by the modulus](character-sums.md)
- [Tails of the twisted harmonic sums](tails.md)

## Sources

- [Apostol, Chapter 6](../../../sources/progressions-locators.md#apostol-chapter-6)
