---
article_id: af_730c4846acb67ae15156a7d9
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.Rank5b.M5b, ZInQ.RouteK.Rank5b.M1, ZInQ.RouteK.Rank5b.Lmat, ZInQ.RouteK.Rank5b.aBit, ZInQ.RouteK.Rank5b.yBit, ZInQ.RouteK.Rank5b.zBit, ZInQ.RouteK.Rank5b.border, ZInQ.RouteK.Rank5b.M1_transpose, ZInQ.RouteK.Rank5b.Config.Lc, ZInQ.RouteK.Rank5b.Config.M1c, ZInQ.RouteK.Rank5b.Config.M5bc, ZInQ.RouteK.Rank5b.Config.M1c_transpose, ZInQ.RouteK.Rank5b.natConfig_bit_eq_aBit, ZInQ.RouteK.Rank5b.natConfig_lam_eq_yBit, ZInQ.RouteK.Rank5b.natConfig_mu_eq_zBit, ZInQ.RouteK.Rank5b.Lmat_eq_Lc, ZInQ.RouteK.Rank5b.M1_eq_M1c, ZInQ.RouteK.Rank5b.M5b_eq_M5bc, ZInQ.RouteK.Rank5b.aBit_add_aBit, ZInQ.RouteK.Rank5b.Lmat_add_transpose_apply
---

# Smith's matrices $L$, $M_1$ and $M_{5b}$

Let $n>0$ be odd and squarefree with prime set $P$. For $p\ne q$ in $P$ put
$a_{pq}=(q/p)_+\in\mathbb F_2$, which is $0$ if $q$ is a square modulo $p$ and $1$ otherwise, and
put $y_p=(-1/p)_+=[p\equiv3\pmod4]$ and $z_p=(2/p)_+=[p\equiv\pm3\pmod8]$. Smith's matrix $L$
(Smith's $A$) is the $P\times P$ matrix over $\mathbb F_2$ with $L_{pq}=a_{pq}$ for $p\ne q$ and
$L_{pp}=\sum_{q\ne p}a_{pq}$, so its rows sum to zero. With $D_z$ the diagonal matrix of the
$z_p$, define the $(P\sqcup P)$-square matrix $M_1$ and its bordering $M_{5b}$:
$$M_1=\begin{pmatrix}L+L^{\mathsf T}&L^{\mathsf T}\\ L&D_z\end{pmatrix},\qquad
M_{5b}=\begin{pmatrix}L+L^{\mathsf T}&L^{\mathsf T}&0\\ L&D_z&y\\ 0&y^{\mathsf T}&0\end{pmatrix},$$
that is, $M_{5b}$ is $M_1$ bordered by the column $(0,y)$, the row $(0,y)^{\mathsf T}$ and a zero
corner. The same matrices are defined for any configuration, with $[q/p]$, $\lambda$, $\mu$ in
place of $a_{pq}$, $y$, $z$, and for $n$ they are those of the configuration of $n$:
$a_{pq}=[q/p]$, $y=\lambda$, $z=\mu$.

$M_1$ is symmetric, and by quadratic reciprocity $a_{pq}+a_{qp}=y_py_q$ for $p\ne q$, so
$L+L^{\mathsf T}$ has entries $y_py_q$ off the diagonal and $0$ on it.

These are the matrices of row 5b of Smith's Table 2; row 5b says that for $n\equiv5\pmod8$ the
determinant of $M_{5b}$ is the genus sum $T_{5b}(n)$ of Tian, Yuan and Zhang ([Theorem 3.6](genus-sum/theorem-3-6.md)
for Rédei's $g$ in Legendre symbols, and with their class numbers through [the agreement of the two
genus sums](../redei/genus-sums-agree.md), by Rédei's formula).

## Depends on

- [The configuration of an odd number and Selmer certificates](../route-k/prime-configuration.md)
- [Configurations](../route-k/configuration.md)

## Sources

- [Notation](../../sources/rank-5b-locators.md#notation)
- [Smith](../../sources/rank-5b-locators.md#smith)
