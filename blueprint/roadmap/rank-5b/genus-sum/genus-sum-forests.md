---
article_id: af_5761acda607c06e6a2c8830e
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.genusSum5b_eq_forest, ZInQ.RouteK.Rank5b.Sec3.markH, ZInQ.RouteK.Rank5b.Sec3.markW_eq, ZInQ.RouteK.Rank5b.Sec3.rootsOf_restrict, ZInQ.RouteK.Rank5b.Sec3.prod_markH_restrict, ZInQ.RouteK.Rank5b.Sec3.even_card_roots, ZInQ.RouteK.Rank5b.Sec3.sum_compat_marked
---

# The genus sum as a forest sum

Let $a,y,z$ be bits on a finite set $V$ that satisfy reciprocity, with $y(V)=0$. Then
$$T_{5b}=\sum_f\Bigl(\sum_{k\in R}y_kz^{R\setminus k}\Bigr)\mathrm{wt}(f)\prod_{\rho\in R}y(T_\rho),$$
the sum over the forests $f$ on $V$, with $R$ the root set of $f$, $z^S=\prod_{\rho\in S}z_\rho$
and $T_\rho$ the tree of $\rho$.

Along the way, for a forest $f$ on $V$ with root set $R$: if $y(V)=0$ and every tree has
$y(T_\rho)=1$, then $|R|$ is even; and if $|R|$ is even, then summing over the set partitions $\pi$
compatible with $f$ and over the marked blocks $B_7\ne B_3$ of $\pi$ the product of the root factors
$\prod_{B\in\pi}e_B(B\cap R)$ gives $\sum_{k\in R}y_kz^{R\setminus k}$, for any bits $y,z$. For any
$B\subseteq V$, the roots of the restriction $f|_B$ (the points of $B$ fixed by $f$) are the roots
of $f$ in $B$.

**Proof sketch.** Start from the marked form of $T_{5b}$, with $w_7$ on $B_7$, $w_3$ on $B_3$ and
$w_1$ on the other blocks. Write each block weight as a forest sum on its block, with one root for
$w_7,w_3$ and two roots for $w_1$, and glue along $\pi$: each marked product becomes a sum over the
forests $f$ on $V$ compatible with $\pi$. For such $f$ the roots of $f|_B$ are the roots of $f$ in
$B$, its trees are those of $f$, and the products over the blocks of the factors indexed by
$B\cap R$ multiply to products over $R$; so the glued term is
$\bigl(\prod_Be_B(B\cap R)\bigr)\,\mathrm{wt}(f)\prod_{\rho\in R}y(T_\rho)$. Exchange the sums and fix
$f$ with $\prod_\rho y(T_\rho)\ne0$. Then every tree has $y(T_\rho)=1$, and since $V$ is the union of
the trees, $|R|\equiv y(V)=0\pmod2$. For a compatible partition the marked sum of the root factors
is a sum over pairs of roots $\rho_7\ne\rho_3$: the term is $(y_{\rho_7}+z_{\rho_7})z^{R\setminus\rho_7}$
if $\rho_7$ and $\rho_3$ are the only roots of their blocks and every other block holds exactly two
roots, and $0$ otherwise. For fixed $(\rho_7,\rho_3)$ these partitions are as many as the pairings
of $R\setminus\{\rho_7,\rho_3\}$, an odd number since $|R|-2$ is even. Summing over the $|R|-1$
choices of $\rho_3$, again an odd number, leaves
$\sum_{\rho_7\in R}(y_{\rho_7}+z_{\rho_7})z^{R\setminus\rho_7}$, which is
$\sum_ky_kz^{R\setminus k}+|R|\,z^R=\sum_ky_kz^{R\setminus k}$.

## Depends on

- [The genus sum $T_{5b}$](genus-sum.md)
- [Forests on a finite set](../forests/forests.md)
- [The root factors of a marked partition](marked-roots.md)
- [Set partitions compatible with a forest](../forests/compatible-partitions.md)

## Proof depends on

- [Partition sums with marked blocks](marked-sums.md)
- [Block weights as forest sums](block-weights.md)
- [Gluing forests along a set partition](../forests/gluing.md)
- [Pairings are odd in number exactly on sets of even size](../forests/pairings.md)

## Sources

- [Theorem 3.6](../../../sources/rank-5b-locators.md#theorem-36)
- [Row 5b of Smith's table](../../../sources/rank-5b-locators.md#row-5b-of-smiths-table)
