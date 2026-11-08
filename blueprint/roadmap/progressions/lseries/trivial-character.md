---
article_id: af_c970c8ff7cac51210174afcd
declaration: theorem
origin: background
---

# The principal $L$-function to the right of $1$

Let $q\ge1$ and let $\chi_0$ be the principal Dirichlet character modulo $q$. For every real
$x>0$,
$$|L(1+x,\chi_0)|\le1+\frac1x .$$

**Proof sketch.** For real $s=1+x>1$, $L(s,\chi_0)=\sum_{n\ge1}\chi_0(n)n^{-s}$ with
$0\le\chi_0(n)\le1$, so $|L(s,\chi_0)|\le\sum_{n\ge1}n^{-s}\le1+\int_1^\infty t^{-s}\,dt
=1+1/x$, comparing each term $n^{-s}$, $n\ge2$, with $\int_{n-1}^nt^{-s}\,dt$.

## Depends on

None.

## Sources

- [Apostol, Chapter 3](../../../sources/progressions-locators.md#apostol-chapter-3)
