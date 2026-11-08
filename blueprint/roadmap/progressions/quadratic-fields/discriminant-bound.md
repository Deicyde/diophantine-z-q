---
article_id: af_408ab79c9adbebe7cffb238a
declaration: theorem
origin: background
---

# The discriminant of $\mathbb Q(\sqrt d)$

Let $d$ be a squarefree integer with $d\ne1$, and let $D_K$ be the discriminant of the ring
of integers of $K=\mathbb Q(\sqrt d)$. Then
$$|D_K|\le4|d| .$$

**Proof sketch.** The order $\mathbb Z[\sqrt d]$ lies in the ring of integers
$\mathcal O_K$, and its discriminant, that of the basis $1,\sqrt d$, is
$\det\begin{pmatrix}2&0\\0&2d\end{pmatrix}=4d$. For a full-rank subring,
$\mathrm{disc}(\mathbb Z[\sqrt d])=[\mathcal O_K:\mathbb Z[\sqrt d]]^2D_K$, so
$|D_K|\le4|d|$. (In fact $D_K=d$ if $d\equiv1\pmod4$ and $4d$ otherwise.)

## Depends on

- [The quadratic field $\mathbb Q(\sqrt d)$](quadratic-field.md)

## Sources

- [Marcus, Chapter 2](../../../sources/progressions-locators.md#marcus-chapter-2)
