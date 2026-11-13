---
article_id: af_875569043402ff6fc05e161f
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.kernel_trivial_iff_redeiG, ZInQ.RouteK.Redei.redeiK_det_updateCol, ZInQ.RouteK.Redei.redeiK_ker_iff_det
---

# Rédei's bit as the triviality of a kernel

Let $V$ be a finite set with bits $a_{ij},y_i,z_i\in\mathbb F_2$ satisfying reciprocity, and let
$B\subseteq V$ be nonempty. Then the kernel of $(L_B\mid z_B)$ is trivial (the column $z_B$
counting only when $y(B)=0$) if and only if $g(B)=1$, where
$$g(B)=\sum_{\rho\in B}y_\rho\,\kappa_\rho(B)\ \text{ if }y(B)=1,\qquad
g(B)=\sum_{\rho\in B}z_\rho\,\kappa_\rho(B)\ \text{ if }y(B)=0,$$
and $\kappa_\rho(B)=\det L_B[B\setminus\rho,B\setminus\rho]$.

Along the way, without reciprocity:

- for $\rho\in B$ and any $w:V\to\mathbb F_2$, the matrix $L_B$ with column $\rho$ replaced by $w$
  has determinant $\sum_{v\in B}w_v\,\kappa_v(B)$ on $B\times B$;
- a square matrix $N$ on $B$ has trivial kernel, in the sense that every $F:V\to\mathbb F_2$
  vanishing off $B$ with $\sum_{p\in B}N_{qp}F_p=0$ for all $q\in B$ vanishes on $B$, if and only
  if its determinant on $B\times B$ is nonzero.

**Proof sketch.** Fix $\rho\in B$, let $w=y$ if $y(B)=1$ and $w=z$ otherwise, and let $N$ be
$L_B$ with column $\rho$ replaced by $w$. By
[the kernel through a square matrix](kernel-square-matrix.md), the kernel of $(L_B\mid z_B)$ is
trivial if and only if $N$ has trivial kernel on $B$, that is, $\det N\ne0$. Expanding $\det N$
along column $\rho$, the minor of $L_B$ with row $v$ and column $\rho$ deleted is $\kappa_v(B)$
(Lemma 2.2(2)), so $\det N=\sum_{v\in B}w_v\kappa_v(B)$, which is $g(B)$ by its definition. In
$\mathbb F_2$, nonzero means $1$.

## Depends on

- [Rédei's $g$ from the bits](../../rank-5b/genus-sum/redei-g.md)
- [The kernel of $(L_B\mid z_B)$ through a square matrix](kernel-square-matrix.md)

## Proof depends on

- [The cofactors of the Laplacian (Lemma 2.2)](../../rank-5b/genus-sum/lemma-2-2.md)
- [Minors over $\mathbb F_2$ as permanents](../../rank-5b/forests/permanent-minors.md)
- [Row operations on minors over $\mathbb F_2$](../../rank-5b/forests/row-operations.md)

## Sources

- [Step 7: the kernel](../../../sources/redei-locators.md#step-7-the-kernel)
- [Rédei's formulas](../../../sources/redei-locators.md#redeis-formulas)
