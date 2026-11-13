---
article_id: af_9528cea159957c45e59e375c
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.det_M1G_eq_class3, ZInQ.RouteK.Rank5b.Sec3.det_M1G_eq_zero, ZInQ.RouteK.Rank5b.Sec3.det_Pmat_eq_class3, ZInQ.RouteK.Rank5b.Sec3.sum_class3_eq_forest, ZInQ.RouteK.Rank5b.Sec3.blockH_restrict, ZInQ.RouteK.Rank5b.Sec3.prod_blockH_restrict, ZInQ.RouteK.Rank5b.Sec3.sum_prod_uniform
---

# $\det M_1$ as a sum over partitions into class-3 blocks (Proposition 3.3)

Let $a,y,z$ be bits on a finite set $V$ that satisfy reciprocity. Then
$$\det P(z,y)=\sum_{\pi}\prod_{B\in\pi}g(B)=\sum_f z^R\,\mathrm{wt}(f)\prod_{\rho\in R}y(T_\rho),$$
the first sum over the set partitions $\pi$ of $V$ into blocks of class $3$, the second over the
forests $f$ on $V$, with $R$ the root set of $f$. If $y(V)=0$, then $\det M_1$ is the same sum over
the partitions into blocks of class $3$; if $y(V)=1$, then $\det M_1=0$.

The forest sum behind it: for every $k$,
$$\sum_\pi\prod_{B\in\pi}\ \sum_{h\text{ with }k\text{ roots}}z^{S(h)}\,\mathrm{wt}(h)\,Y(h)
=\sum_fN_k(f)\,z^R\,\mathrm{wt}(f)\prod_{\rho\in R}y(T_\rho),$$
where $h$ runs over the forests on the block $B$ with exactly $k$ roots, $S(h)$ is the root set of
$h$, $Y(h)$ is the product of the sums of $y$ over its trees, and $N_k(f)$ is the number of set
partitions compatible with $f$ in which every block contains exactly $k$ roots.

**Proof sketch.** For the forest sum, glue along $\pi$: the product over the blocks of the
forest sums is a sum over the forests $f$ on $V$ compatible with $\pi$, and for such $f$ the
product of the block terms of the restrictions $f|_B$ is $z^R\,\mathrm{wt}(f)\prod_{\rho\in R}y(T_\rho)$ if every block holds exactly
$k$ roots and $0$ otherwise. Exchanging the sums gives the coefficient $N_k(f)$.

Now take $k=1$. For a set partition $\pi$, $\prod_{B\in\pi}w_3(B)$ is $\prod_Bg(B)$ if all blocks have
class $3$ and $0$ otherwise, and each $w_3(B)$ is the sum over the forests on $B$ with one root
$\rho$ of $z_\rho\,\mathrm{wt}(h)\,Y(h)$. So the class-3 partition sum is
$\sum_fN_1(f)\,z^R\,\mathrm{wt}(f)\prod_\rho y(T_\rho)$, and $N_1(f)=1$, since exactly one partition
compatible with $f$ has one root in every block, the partition into the trees of $f$. Grouping
the forests by their root sets, the forest expansion of $\det P(z,y)$ is the same sum. Finally
$\det M_1=(1+y(V))\det P(z,y)$.

## Depends on

- [The row-5b determinant as a forest sum](det-m5b-forests.md)
- [The genus sum $T_{5b}$](genus-sum.md)
- [The determinant of $P(c,d)$ as a forest sum](../forests/det-p-forests.md)
- [Forests on a finite set](../forests/forests.md)
- [Block weights as forest sums](block-weights.md)
- [Set partitions compatible with a forest](../forests/compatible-partitions.md)

## Proof depends on

- [Gluing forests along a set partition](../forests/gluing.md)
- [Compatible partitions with one or two roots per block](roots-per-block.md)
- [The genus sum as a forest sum](genus-sum-forests.md)

## Sources

- [Propositions 3.3 and 3.4](../../../sources/rank-5b-locators.md#propositions-33-and-34)
