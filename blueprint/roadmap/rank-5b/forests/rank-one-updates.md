---
article_id: af_c8086e0cc6c1b01a7d3c3ef0
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.det_add_col_mul_row_of_mulVec, ZInQ.RouteK.Rank5b.Sec3.det_add_col_mul_row, ZInQ.RouteK.Rank5b.Sec3.det_updateCol_finset_sum, ZInQ.RouteK.Rank5b.Sec3.rowPiece, ZInQ.RouteK.Rank5b.Sec3.rowPiece_row, ZInQ.RouteK.Rank5b.Sec3.det_rowPiece_eq_zero, ZInQ.RouteK.Rank5b.Sec3.det_border_zmod2, ZInQ.RouteK.Rank5b.Sec3.quad_symm_zmod2, ZInQ.RouteK.Rank5b.Sec3.zmod2_neg, ZInQ.RouteK.Rank5b.Sec3.zmod2_sub, ZInQ.RouteK.Rank5b.Sec3.zmod2_mul_self
---

# Rank-one updates and bordered determinants

Let $K$ be a field, $I$ a finite index set, $A$ an $I\times I$ matrix over $K$ and
$u,w\in K^I$. Write $A^{(j\leftarrow u)}$ for $A$ with column $j$ replaced by $u$. Then
$$\det(A+uw^{\mathsf T})=\det A+\sum_{j\in I}w_j\det A^{(j\leftarrow u)}.$$
If moreover $Ax=u$ for some $x\in K^I$, then
$$\det(A+uw^{\mathsf T})=\det A\,(1+w\cdot x).$$
No invertibility is assumed. The determinant is additive in a column over finite sums: if column
$j$ of $A$ is replaced by $\sum_{u\in T}f_u$, the determinant is
$\sum_{u\in T}\det A^{(j\leftarrow f_u)}$.

Over $\mathbb F_2$, where $-t=t$, $s-t=s+t$ and $t^2=t$:

- for an $I\times I$ matrix $A$ and $v\in\mathbb F_2^I$, the bordered matrix
  $\begin{pmatrix}A&v\\v^{\mathsf T}&0\end{pmatrix}$, indexed by $I$ and one more index, has
  determinant $\det(A+vv^{\mathsf T})+\det A$;
- for a symmetric $I\times I$ matrix $B$ and $v\in\mathbb F_2^I$,
  $\sum_{i,j}v_iv_jB_{ij}=\sum_iv_iB_{ii}$.

**Proof sketch.** Transpose: row $i$ of $A^{\mathsf T}+wu^{\mathsf T}$ is row $i$ of
$A^{\mathsf T}$ plus $w_iu^{\mathsf T}$. By multilinearity in the rows, the determinant is the sum,
over the sets $s$ of rows, of the determinant of the matrix whose rows in $s$ are those of
$A^{\mathsf T}$ and whose other rows are $w_iu^{\mathsf T}$. If two rows lie outside $s$ the term
vanishes: the two rows are multiples of $u^{\mathsf T}$, so one of them is zero or a multiple of
the other. What remains is $s=I$, giving $\det A$, and $s=I\setminus\{j\}$, giving
$w_j\det A^{(j\leftarrow u)}$. If $Ax=u$, then $u=\sum_kx_k(\text{column }k)$; by linearity in
column $j$, and since the terms with $k\ne j$ have two equal columns,
$\det A^{(j\leftarrow u)}=x_j\det A$, which gives the second formula. For the bordered matrix,
the matrix with corner $1$ in place of $0$ has determinant $\det(A-vv^{\mathsf T})=
\det(A+vv^{\mathsf T})$, by the Schur complement of the corner. Its last row is the last row of the
bordered matrix plus $(0,\dots,0,1)$, so by linearity in the last row it is also the bordered
determinant plus the determinant of a block triangular matrix with diagonal blocks $A$ and $1$,
that is, plus $\det A$. For the quadratic form, the terms $(i,j)$ and $(j,i)$ with $i\ne j$ are
equal by symmetry and cancel, and $v_i^2=v_i$.

## Depends on

None.

## Sources

- [Propositions 3.3 and 3.4](../../../sources/rank-5b-locators.md#propositions-33-and-34)
