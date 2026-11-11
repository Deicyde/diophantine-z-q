---
article_id: af_c9f3d88e94b5cc89db893959
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.sum_marked_eq_roots, ZInQ.RouteK.Rank5b.Sec3.markE, ZInQ.RouteK.Rank5b.Sec3.prod_parts_inter
---

# The root factors of a marked partition

Let $y,z$ be bits on a finite set $V$, $f$ a forest on $V$ with root set $R$, and write
$z^S=\prod_{\rho\in S}z_\rho$. For blocks $B_7,B_3$ and a block $B$, the *root factor* $e_B(S)$ of a
set $S$ is $y_\rho+z_\rho$ if $B=B_7$ and $S=\{\rho\}$; $z_\rho$ if $B=B_3\ne B_7$ and $S=\{\rho\}$;
$z^S$ if $B\notin\{B_7,B_3\}$ and $|S|=2$; and $0$ in all other cases.

For a set partition $\pi$ of $V$ compatible with $f$,
$$\sum_{B_7\in\pi}\ \sum_{B_3\in\pi,\,B_3\ne B_7}\ \prod_{B\in\pi}e_B(B\cap R)
=\sum_{\rho_7\in R}\ \sum_{\rho_3\in R,\,\rho_3\ne\rho_7}[\pi\in A(\rho_7,\rho_3)]\,
(y_{\rho_7}+z_{\rho_7})\,z^{R\setminus\rho_7},$$
where $A(\rho_7,\rho_3)$ is the set of compatible partitions in which $\rho_7$ and $\rho_3$ are each the
only root of their block and the block of every other root contains exactly two roots.

Along the way: for any set partition $\pi$ of $V$, any $S\subseteq V$ and any $\varphi:V\to\mathbb F_2$,
$\prod_{B\in\pi}\prod_{i\in B\cap S}\varphi(i)=\prod_{i\in S}\varphi(i)$.

**Proof sketch.** The last identity holds because the sets $B\cap S$, $B\in\pi$, are disjoint with
union $S$. For the main identity, every block of a compatible partition contains a root, and the
block of a root determines it. A marked product $\prod_Be_B(B\cap R)$ is nonzero only if $B_7$ and
$B_3$ each contain exactly one root, $\rho_7$ and $\rho_3$, and every other block exactly two; then
$\pi\in A(\rho_7,\rho_3)$, $B_7$ and $B_3$ are the blocks of $\rho_7$ and $\rho_3$, and the product is
$(y_{\rho_7}+z_{\rho_7})\,z_{\rho_3}\prod z^{B\cap R}$ over the other blocks, which is
$(y_{\rho_7}+z_{\rho_7})\,z^{R\setminus\rho_7}$ by the last identity. So the pairs of distinct blocks
with nonzero product correspond to the pairs of distinct roots $(\rho_7,\rho_3)$ with
$\pi\in A(\rho_7,\rho_3)$, with the same terms.

## Depends on

- [Forests on a finite set](../forests/forests.md)
- [Set partitions compatible with a forest](../forests/compatible-partitions.md)

## Sources

- [Theorem 3.6](../../../sources/rank-5b-locators.md#theorem-36)
