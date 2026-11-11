---
article_id: af_a8ed25ba8f798d8030f44345
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.det_M5bG_eq_class73, ZInQ.RouteK.Rank5b.Sec3.markE', ZInQ.RouteK.Rank5b.Sec3.prod_markW'_eq, ZInQ.RouteK.Rank5b.Sec3.sum_marked'_eq
---

# $\det M_{5b}$ as a sum over partitions into class-7 and class-3 blocks (Proposition 3.4)

Let $a,y,z$ be bits on a finite set $V$ that satisfy reciprocity and $y(V)=0$. Then
$$\det M_{5b}=\sum_\pi\prod_{B\in\pi}g(B),$$
the sum over the set partitions $\pi$ of $V$ with exactly one block of class $7$ and all other
blocks of class $3$.

Along the way, with $m'_{B_7}$ equal to $w_7$ on $B_7$ and $w_3$ on every other block: under
reciprocity each marked product $\prod_{B\in\pi}m'_{B_7}(B)$ is a sum over the forests on $V$
compatible with $\pi$, as in the proof below. For a forest $f$ on $V$ with root set
$R$ and a set partition $\pi$ compatible with $f$, the marked sum of the root factors (for each
block, $y_\rho+z_\rho$ on $B_7$ and $z_\rho$ on the others when the block contains the single root
$\rho$, and $0$ when it contains another number of roots) is
$\sum_{\rho_7\in R}(y_{\rho_7}+z_{\rho_7})z^{R\setminus\rho_7}$ if every block of $\pi$ contains exactly one
root, and $0$ otherwise.

**Proof sketch.** The partition sum is the marked sum
$\sum_\pi\sum_{B_7\in\pi}\prod_{B\in\pi}m'_{B_7}(B)$ over all set partitions. Write $w_7$ and $w_3$
as forest sums with one root per block and glue along $\pi$; each marked product becomes a sum over the forests $f$ compatible with $\pi$ of the
product of the root factors times $\mathrm{wt}(f)\prod_{\rho\in R}y(T_\rho)$. Exchanging the sums, the
coefficient of $f$ is the sum, over the compatible partitions with exactly one root per block, of
$\sum_{\rho_7\in R}(y_{\rho_7}+z_{\rho_7})z^{R\setminus\rho_7}$. Exactly one compatible partition has one
root in every block, the partition into the trees of $f$. If $\prod_\rho y(T_\rho)\ne0$, then $|R|$ is even because
$y(V)=0$, so $\sum_\rho z_\rho z^{R\setminus\rho}=|R|\,z^R$ vanishes and the coefficient is
$\sum_{k\in R}y_kz^{R\setminus k}$. This is the coefficient of $f$ in the forest form of $\det M_{5b}$,
where $1+y(V)=1$, after grouping the forests by their root sets.

## Depends on

- [The row-5b determinant as a forest sum](det-m5b-forests.md)
- [The genus sum $T_{5b}$](genus-sum.md)
- [Block weights as forest sums](block-weights.md)
- [Set partitions compatible with a forest](../forests/compatible-partitions.md)
- [Forests on a finite set](../forests/forests.md)

## Proof depends on

- [$\det M_1$ as a sum over partitions into class-3 blocks (Proposition 3.3)](proposition-3-3.md)
- [The genus sum as a forest sum](genus-sum-forests.md)
- [Gluing forests along a set partition](../forests/gluing.md)
- [Partition sums with marked blocks](marked-sums.md)
- [Compatible partitions with one or two roots per block](roots-per-block.md)

## Sources

- [Propositions 3.3 and 3.4](../../../sources/rank-5b-locators.md#propositions-33-and-34)
