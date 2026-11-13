---
article_id: af_050c8b5ea0acafe99fe3bc8f
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.det_M5bG_forest, ZInQ.RouteK.Rank5b.Sec3.det_M5bG, ZInQ.RouteK.Rank5b.Sec3.det_M1G, ZInQ.RouteK.Rank5b.Sec3.M1G, ZInQ.RouteK.Rank5b.Sec3.M5bG, ZInQ.RouteK.Rank5b.Sec3.M5b_eq_M5bG, ZInQ.RouteK.Rank5b.Sec3.lapl_rowSum, ZInQ.RouteK.Rank5b.Sec3.M1G_eq, ZInQ.RouteK.Rank5b.Sec3.Pmat_mulVec, ZInQ.RouteK.Rank5b.Sec3.dot_elim, ZInQ.RouteK.Rank5b.Sec3.col_row_mulVec, ZInQ.RouteK.Rank5b.Sec3.adjugate_Pmat_inr
---

# The row-5b determinant as a forest sum

Let $a,y,z$ be bits on a finite set $V$ and $L=L_V$ their Laplacian on $V$; its rows sum to zero.
Define the $(V\sqcup V)$-square matrix $M_1$ and its bordering $M_{5b}$ from the bits as in Smith's
matrices:
$$M_1=\begin{pmatrix}L+L^{\mathsf T}&L^{\mathsf T}\\ L&D_z\end{pmatrix},\qquad
M_{5b}=\begin{pmatrix}M_1&(0,y)\\ (0,y)^{\mathsf T}&0\end{pmatrix}.$$
For the bits of a natural number $n$ these are Smith's $M_1$ and $M_{5b}$. Let
$P(c,d)=\begin{pmatrix}D_d&L^{\mathsf T}\\ L&D_c\end{pmatrix}$ for $c,d\in\mathbb F_2^V$, the matrix
whose determinant is [a sum over forests](../forests/det-p-forests.md), write $z[k\mapsto t]$ for $z$ with the entry at $k$ replaced by $t$, $z^S$ for
$\prod_{\rho\in S}z_\rho$, and $\mathbf 1$ for the all-ones vector on $V$.

1. For all $c,d\in\mathbb F_2^V$, $P(c,d)\,(\mathbf 1,0)=(d,0)$, and the diagonal entry of the
   adjugate of $P(c,d)$ at the lower copy $k'$ of $k\in V$ is
   $\operatorname{adj}P(c,d)_{k'k'}=\det P(c[k\mapsto1],d)+\det P(c[k\mapsto0],d)$.
2. Under reciprocity, $M_1=P(z,y)+ww^{\mathsf T}$ with $w=(y,0)$, and
   $$\det M_1=(1+y(V))\det P(z,y).$$
3. Under reciprocity,
   $$\det M_{5b}=(1+y(V))\sum_{k\in V}y_k\bigl(\det P(z[k\mapsto1],y)+\det P(z[k\mapsto0],y)\bigr)$$
   and
   $$\det M_{5b}=(1+y(V))\sum_{F\subseteq V}\Bigl(\sum_{k\in F}y_kz^{F\setminus k}\Bigr)
   \sum_f\mathrm{wt}(f)\prod_{\rho\in F}y(T_\rho),$$
   the inner sum over the forests $f$ on $V$ rooted at $F$, with $T_\rho$ the tree of $\rho$.

**Proof sketch.** (1) The rows of $L$ sum to zero, so $P(c,d)(\mathbf 1,0)=(d,0)$. Row $k'$ of
$P(c[k\mapsto1],d)$ is row $k'$ of $P(c[k\mapsto0],d)$ plus the unit vector at $k'$; by linearity in
that row, the difference of the two determinants is the determinant with row $k'$ replaced by the
unit vector, which is $\operatorname{adj}P_{k'k'}$ and does not depend on $c_k$. (2) By reciprocity
$L+L^{\mathsf T}$ has entries $y_iy_j$ off the diagonal and $0$ on it, while $(ww^{\mathsf T})_{ii}=y_i^2=y_i$
cancels the diagonal of $D_y$; so $M_1=P(z,y)+ww^{\mathsf T}$. With $x=(\mathbf 1,0)$ we have $P(z,y)x=w$, and
the rank-one update with a preimage gives $\det M_1=\det P(z,y)\,(1+w\cdot x)=(1+y(V))\det P(z,y)$.
(3) Put $P=P(z,y)$ and $v=(0,y)$. The bordered determinant is
$\det M_{5b}=\det(M_1+vv^{\mathsf T})+\det M_1$. Since $v\cdot x=0$, also $(P+vv^{\mathsf T})x=w$, so
$\det(M_1+vv^{\mathsf T})=(1+y(V))\det(P+vv^{\mathsf T})$. Expanding $\det(P+vv^{\mathsf T})$ by the rank-one
formula, the term $\det P$ cancels against $\det M_1$, and
$\det M_{5b}=(1+y(V))\sum_jv_j\det P^{(j\leftarrow v)}$, with $P^{(j\leftarrow v)}$ the matrix $P$ with
column $j$ replaced by $v$. Expanding that column gives $\sum_{i,j}v_iv_j\operatorname{adj}(P)_{ij}$. The
adjugate of the symmetric matrix $P$ is symmetric, so over $\mathbb F_2$ this is
$\sum_iv_i\operatorname{adj}(P)_{ii}=\sum_ky_k\operatorname{adj}(P)_{k'k'}$, and (1) gives the first formula.
For the second, insert the forest expansion of $\det P(z[k\mapsto t],y)$ and use
$\prod_{\rho\in F}z[k\mapsto1]_\rho+\prod_{\rho\in F}z[k\mapsto0]_\rho=[k\in F]\,z^{F\setminus k}$.

## Depends on

- [Smith's matrices $L$, $M_1$ and $M_{5b}$](../smith-matrices.md)
- [Rédei's $g$ from the bits](redei-g.md)
- [Forests on a finite set](../forests/forests.md)
- [The determinant of $P(c,d)$ as a forest sum](../forests/det-p-forests.md)

## Proof depends on

- [Rank-one updates and bordered determinants](../forests/rank-one-updates.md)

## Sources

- [Propositions 3.3 and 3.4](../../../sources/rank-5b-locators.md#propositions-33-and-34)
