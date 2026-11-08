---
article_id: af_455467c87f8064f2f0feb4a7
declaration: def
origin: background
---

# The ideal counting function

Let $K$ be a number field with ring of integers $\mathcal O_K$. For $n\ge1$ let $a_K(n)$ be
the number of ideals $I\subseteq\mathcal O_K$ of absolute norm $N(I)=|\mathcal O_K/I|=n$.
This number is finite, and the Dedekind zeta function is the Dirichlet series
$$\zeta_K(s)=\sum_{n\ge1}a_K(n)\,n^{-s},$$
absolutely convergent for $\mathrm{Re}\,s>1$.

**Proof sketch.** An ideal of norm $n$ contains $n$, and $\mathcal O_K/n\mathcal O_K$ is
finite, so there are finitely many. Absolute convergence for $\mathrm{Re}\,s>1$ is part of
the class number formula's setting (the number of ideals of norm at most $t$ is
$O(t)$).

## Depends on

None.

## Sources

- [Marcus, Chapter 7](../../../sources/progressions-locators.md#marcus-chapter-7)
