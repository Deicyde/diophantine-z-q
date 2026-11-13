---
article_id: af_2fa68b68eab2cf0fe4c91881
declaration: def
origin: background
statement: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.lapl
---

# The Laplacian of a family of bits

Let $V$ be a finite set and $a=(a_{ij})_{i,j\in V}$ a family of bits $a_{ij}\in\mathbb F_2$. For
$U\subseteq V$ the *Laplacian* of $a$ on $U$ is the $V\times V$ matrix $L_U$ over $\mathbb F_2$
with
$$(L_U)_{ij}=a_{ij}\quad(i\ne j),\qquad (L_U)_{ii}=\sum_{k\in U,\,k\ne i}a_{ik}.$$
Only the diagonal depends on $U$: the diagonal entry in row $i$ is the sum of the bits of that row
over the columns in $U$ other than $i$, also when $i\notin U$. The bits $a_{ii}$ are never used.
We write $L=L_V$.

For the bits $a_{pq}$ of an odd squarefree number, $L_V$ is [Smith's matrix $L$](../smith-matrices.md): the two
definitions agree entry by entry.

## Depends on

None.

## Sources

- [Notation](../../../sources/rank-5b-locators.md#notation)
- [Lemma 2.1](../../../sources/rank-5b-locators.md#lemma-21)
