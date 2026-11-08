---
article_id: af_e280a7ecf164acebf9c98268
declaration: theorem
origin: background
---

# Higher prime powers contribute little

For every real $x$,
$$\sum_{\substack{n\le x\\ n\text{ not prime}}}\frac{\Lambda(n)}{n}\le3 ,$$
that is, the prime powers $p^k$ with $k\ge2$ contribute at most $3$ to
$\sum_{n\le x}\Lambda(n)/n$.

**Proof sketch.** The sum is at most
$\sum_p\sum_{k\ge2}\log p/p^k=\sum_p\log p/(p(p-1))\le\sum_{m\ge2}\log m/(m(m-1))$. With
$\log m\le\sqrt m$ each term is at most $1/(\sqrt m(m-1))$, and
$1/(\sqrt m(m-1))\le\sqrt2\,\bigl(2/\sqrt{m-1}-2/\sqrt m\bigr)$ for $m\ge2$ (equivalent to
$\sqrt m\le(2\sqrt2-1)\sqrt{m-1}$). The series telescopes to at most $2\sqrt2<3$.

## Depends on

None.

## Sources

- [Apostol, Chapter 4](../../../sources/progressions-locators.md#apostol-chapter-4)
