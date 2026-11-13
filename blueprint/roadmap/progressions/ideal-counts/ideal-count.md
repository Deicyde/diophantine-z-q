---
article_id: af_455467c87f8064f2f0feb4a7
declaration: def
origin: background
statement: formalized
lean: ZInQ.Progressions.idealCount, ZInQ.Progressions.dedekindZeta_eq_LSeries_idealCount, ZInQ.Progressions.IdealCount.LSeriesSummable_idealCount
---

# The ideal counting function

Let $K$ be a number field with ring of integers $\mathcal O_K$. For $n\ge0$ let $a_K(n)$ be
the number of ideals $I\subseteq\mathcal O_K$ of absolute norm $N(I)=|\mathcal O_K/I|=n$.
This number is finite, and the Dedekind zeta function is the Dirichlet series
$$\zeta_K(s)=\sum_{n\ge1}a_K(n)\,n^{-s},$$
absolutely convergent for $\mathrm{Re}\,s>1$.

**Proof sketch.** There are finitely many ideals of norm at most $n$, because
$\mathcal O_K$ has finite quotients. The Dirichlet series is the definition of $\zeta_K$.
Absolute convergence for $\mathrm{Re}\,s>1$ follows from the asymptotic count of ideals of
norm at most $t$, which is $O(t)$ (it is $\kappa_Kt+o(t)$, the input to the class number
formula), by partial summation.

## Depends on

None.

## Sources

- [Marcus, Chapter 7](../../../sources/progressions-locators.md#marcus-chapter-7)
