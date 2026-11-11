---
article_id: af_28f941d42cb102601355fd38
---

# Row 5b of Smith's table

Row 5b of Smith's Table 2 says that for squarefree $n\equiv5\pmod8$ the determinant of $M_{5b}$ is the
genus sum $T_{5b}(n)$ of Tian, Yuan and Zhang (Theorem 3.6). Here Rédei's $g$ is defined from the
bits through the cofactors $\kappa_\rho(B)$ of the Laplacian of a block, so both sides depend only on
the bits $a_{pq}$, $y_p$, $z_p$ of the primes of $n$. That this $g$ is the parity of a class number
is [Rédei's formula](../../redei/redei-formula.md); it is not needed in this section.

Most statements are about bits $a_{ij}$, $y_i$, $z_i$ on an abstract finite set $V$; for the primes of
$n$, $V$ is the set of primes, and the odd number is still written $n$, as in the rest of the
chapter. The proof writes both sides of Theorem 3.6 as the same sum over the forests on $V$. The
determinant goes through a rank-one update and the matrix $P(c,d)$ of [the forests
section](../forests/README.md). The genus sum goes block by block, through Lemma 2.2 and the
cofactor forms (2.1) and (2.2) of $g$, glued along the partition. Only reciprocity
$a_{pq}+a_{qp}=y_py_q$ and $y(V)=0$ are used, and $y(V)=0$ holds since $n$ is squarefree and
$n\equiv1\pmod4$. The partition
forms of Propositions 3.3–3.5 are proved as well, but the proof of Theorem 3.6 does not pass through
them.

## Rédei's $g$ and the genus sum

- [Rédei's $g$ from the bits](redei-g.md)
- [The cofactors of the Laplacian (Lemma 2.2)](lemma-2-2.md)
- [Rédei's $g$ through the cofactors (2.1), (2.2)](redei-g-cofactors.md)
- [The genus sum $T_{5b}$](genus-sum.md)

## Both sides as forest sums

A rank-one update reduces $\det M_1$ to $\det P(z,y)$, and $\det M_{5b}$ to the determinants of
$P(z[k\mapsto1],y)$ and $P(z[k\mapsto0],y)$, $k\in V$. On the other side,
each block weight of the genus sum is a sum over the forests of the block with one or two roots.
Marking the blocks of classes $7$ and $3$ turns the partition sums into sums of products of block
weights, ready to be glued.

- [The row-5b determinant as a forest sum](det-m5b-forests.md)
- [Block weights as forest sums](block-weights.md)
- [Partition sums with marked blocks](marked-sums.md)
- [The root factors of a marked partition](marked-roots.md)
- [The genus sum as a forest sum](genus-sum-forests.md)

## Theorem 3.6

- [The genus sum of an odd number from its bits](genus-sum-bits.md)
- [Row 5b of Smith's table (Theorem 3.6)](theorem-3-6.md)
- [Two values of the genus sum](genus-sum-values.md)

## Propositions 3.3–3.5

The same forest expansions give $\det M_1$ and $\det M_{5b}$ as sums over set partitions, and compare
the sums over the partitions into class-1 blocks and into class-3 blocks.

- [Compatible partitions with one or two roots per block](roots-per-block.md)
- [$\det M_1$ as a sum over partitions into class-3 blocks (Proposition 3.3)](proposition-3-3.md)
- [$\det M_{5b}$ as a sum over partitions into class-7 and class-3 blocks (Proposition 3.4)](proposition-3-4.md)
- [From class-1 blocks to class-3 blocks (Proposition 3.5)](proposition-3-5.md)
