---
article_id: af_ca6bea651737dd1cd52ef8ad
declaration: theorem
origin: background
---

# Character sums are bounded by the modulus

Let $q\ge1$ and let $\chi$ be a nonprincipal Dirichlet character modulo $q$. For every real
$x$,
$$\Bigl|\sum_{1\le n\le x}\chi(n)\Bigr|\le q .$$
More generally $\bigl|\sum_{a<n\le b}\chi(n)\bigr|\le q$ for all integers $0\le a\le b$.

**Proof sketch.** The values of $\chi$ on any $q$ consecutive integers run once through its
values on $\mathbb Z/q\mathbb Z$, whose sum is $0$ because $\chi$ is nonprincipal. Removing
complete blocks of $q$ consecutive integers from the interval leaves fewer than $q$ terms,
each of absolute value at most $1$.

## Depends on

None.

## Sources

- [Apostol, Chapter 6](../../../sources/progressions-locators.md#apostol-chapter-6)
