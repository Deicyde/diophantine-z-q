---
article_id: af_408ab79c9adbebe7cffb238a
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Progressions.Qsqrt.abs_discr_le, ZInQ.Progressions.Qsqrt.exists_four_mul_eq_sq_mul_discr, ZInQ.Progressions.Qsqrt.discr_basis
---

# The discriminant of $\mathbb Q(\sqrt d)$

Let $d$ be an integer that is not the square of a rational number, and let $D_K$ be the
discriminant of the ring of integers of $K=\mathbb Q(\sqrt d)$. Then
$$|D_K|\le4|d| .$$

**Proof sketch.** The trace of $x+y\sqrt d$ is $2x$, so the basis $1,\sqrt d$ has
discriminant $\det\begin{pmatrix}2&0\\0&2d\end{pmatrix}=4d$. Since $\sqrt d$ is integral, the
matrix expressing $1,\sqrt d$ in an integral basis of $\mathcal O_K$ has integer entries, so
$4d=m^2D_K$ with $m$ its determinant, a nonzero integer. Hence $|D_K|\le4|d|$. The ring of
integers is never computed. (In fact, for squarefree $d$, $D_K=d$ if $d\equiv1\pmod4$ and
$4d$ otherwise.)

## Depends on

- [The quadratic field $\mathbb Q(\sqrt d)$](quadratic-field.md)

## Sources

- [Marcus, Chapter 2](../../../sources/progressions-locators.md#marcus-chapter-2)
