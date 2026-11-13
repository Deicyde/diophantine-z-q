---
article_id: af_14a015b9a406181359ff3cb7
---

# Forests and minors over $\mathbb F_2$

Over $\mathbb F_2$ a determinant is a permanent, and the minors of the Laplacian of a family of
bits count forests. This section proves the counting statements that the identity
$T_{5b}(n)=\det M_{5b}$ of row 5b rests on. No arithmetic enters: $V$ is any finite set (for an
odd number $n$, the set of its primes), the bits $a_{ij}\in\mathbb F_2$ are arbitrary, and the Laplacian $L_U$ of the bits on
$U\subseteq V$ is defined here; for the bits of $n$, $L_V$ is Smith's matrix $L$.

There are three main results. The forest lemma, the case over $\mathbb F_2$ of the all-minors
matrix-tree theorem, writes a minor of $L_U$ as a sum over forests. The second expands the
determinant of the symmetric block matrix
$P(c,d)=\begin{pmatrix}D_d&L^{\mathsf T}\\L&D_c\end{pmatrix}$ as a forest sum. The third relates
the forests on $V$ to the set partitions of $V$ whose blocks are unions of trees.

## Minors over $\mathbb F_2$

A minor with rows $R$ and columns $C$ is a sum over the bijections $R\to C$, with no signs; for
$R=C$ it is the principal minor. Two identities, for a rank-one change of a matrix and for a
bordered matrix, serve for the determinants of Smith's matrices.

- [Minors over $\mathbb F_2$ as permanents](permanent-minors.md)
- [Row operations on minors over $\mathbb F_2$](row-operations.md)
- [Rank-one updates and bordered determinants](rank-one-updates.md)

## Forests and the forest lemma

Expanding the diagonal entries of the Laplacian turns a minor into a sum over maps. A map with a
cycle has an even number of compatible bijections and drops out, and each forest contributes once
exactly when the deleted columns meet every tree once.

- [The Laplacian of a family of bits](laplacian.md)
- [Forests on a finite set](forests.md)
- [Expanding the diagonal of a Laplacian](diagonal-expansion.md)
- [Maps with a cycle contribute an even number](cycles-cancel.md)
- [The map $\sigma_W$ and the transversal criterion](transversal-criterion.md)
- [A forest has at most one compatible bijection](forest-bijection.md)
- [The forest lemma (Lemma 2.1)](forest-lemma.md)

## A determinant as a forest sum

Expanding the two diagonal blocks of $P(c,d)$ leaves, for each choice of deleted rows and columns,
the product of a minor of $L$ with its transpose, which over $\mathbb F_2$ is the minor itself; the
forest lemma turns it into forests weighted by their roots and trees.

- [Minors of anti-diagonal block matrices and of diagonal shifts](block-minors.md)
- [The determinant of $P(c,d)$ as a forest sum](det-p-forests.md)

## Forests and set partitions

A family of forests on the blocks of a set partition is a forest on the whole set that preserves
the blocks. The compatible partitions with prescribed numbers of roots per block are counted by
pairings of the roots.

- [Gluing forests along a set partition](gluing.md)
- [Pairings are odd in number exactly on sets of even size](pairings.md)
- [Set partitions compatible with a forest](compatible-partitions.md)
