---
article_id: af_54e095f634bcf554fe3b23f1
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.kappa_add_kappa, ZInQ.RouteK.Rank5b.Sec3.kappa_eq_kappa, ZInQ.RouteK.Rank5b.Sec3.colSum_lapl, ZInQ.RouteK.Rank5b.Sec3.colSum, ZInQ.RouteK.Rank5b.Sec3.pmin_lapl_offdiag, ZInQ.RouteK.Rank5b.Sec3.kappa_eq_forests, ZInQ.RouteK.Rank5b.Sec3.isTransv_pair, ZInQ.RouteK.Rank5b.Sec3.kappa_eq_pmin
---

# The cofactors of the Laplacian (Lemma 2.2)

Let $a$ be bits on a finite set $V$, let $B\subseteq V$, and let $c_v=\sum_{u\in B}(L_B)_{uv}$ be the
column sums of $L_B$ over the rows of $B$. For a forest $\varphi$ and a root $i$ of $\varphi$, $T_i(\varphi)$
is the tree of $i$.

*Cofactors as forest counts.* For $\rho\in V$,
$\kappa_\rho(B)=\operatorname{per}L_B[B\setminus\{\rho\},B\setminus\{\rho\}]$. For $\rho\in B$,
$\kappa_\rho(B)=\sum_f\mathrm{wt}(f)$, the sum over the forests $f$ on $B$ rooted at $\{\rho\}$, that
is, the spanning arborescences of $B$ with root $\rho$.

Under reciprocity, the column sums are $c_v=y_v\,(1+y(B))$ for every $v\in B$. Moreover:

1. Under reciprocity, if $y(B)=1$, then $\kappa_i(B)=\kappa_j(B)$ for all $i,j\in B$.
2. For $i,j\in B$, $\operatorname{per}L_B[B\setminus\{i\},B\setminus\{j\}]=\kappa_i(B)$.
3. (The $\kappa$-difference.) For $i\ne j$ in $B$,
   $$\kappa_i(B)+\kappa_j(B)=\sum_\varphi\mathrm{wt}(\varphi)\sum_{v\in T_i(\varphi)}c_v,$$
   the sum over the forests $\varphi$ on $B$ rooted at $\{i,j\}$.

Along the way: for $i\ne j$ in $B$, $v\in B$ with $v\ne j$ and a forest $\varphi$ on $B$ rooted at
$\{i,j\}$, the set $\{j,v\}$ is a transversal of $\varphi$ if and only if $v$ lies in the tree of $i$.

**Proof sketch.** *Forest counts.* The principal minor is a permanent over $\mathbb F_2$. For
$\rho\in B$, apply the forest lemma with $U=B$ and $F=W=\{\rho\}$: a forest rooted at $\{\rho\}$ has
the single tree $B$, so $\{\rho\}$ is always a transversal. *Column sums.* The diagonal entry of
column $v$ is $\sum_{u\in B,u\ne v}a_{vu}$, so
$c_v=\sum_{u\in B,u\ne v}(a_{vu}+a_{uv})=\sum_{u\in B,u\ne v}y_vy_u=y_v(y(B)+y_v)=y_v(1+y(B))$, using
$y_v^2=y_v$. (2) The forest lemma with $F=\{i\}$ and $W=\{j\}$; again $j$ lies in the single tree.
(3) Put $R=B\setminus\{j\}$, so that $\kappa_j(B)=\operatorname{per}L_B[R,R]$. Replace row $i$ by the
sum of all rows of $R$. By linearity in that row the minor changes by the minors with row $i$
replaced by another row of $R$, and these vanish because they have two equal rows. The sum of the
rows of $R$ is $c+(L_B)_{j,\cdot}$, so by linearity $\kappa_j(B)$ is the minor with row $i$ replaced by
$(L_B)_{j,\cdot}$ plus the minor with row $i$ replaced by $c$. Expanding the first along that row and
comparing with the expansion of (2) along row $j$ gives $\kappa_i(B)$. Expanding the second along the
row $c$ gives $\sum_{v\in R}c_v\operatorname{per}L_B[B\setminus\{i,j\},B\setminus\{j,v\}]$. By the
forest lemma with $F=\{i,j\}$ and $W=\{j,v\}$, and the transversal criterion above, each of these
minors is the sum of $\mathrm{wt}(\varphi)$ over the forests $\varphi$ rooted at $\{i,j\}$ with $v$ in the
tree of $i$. Exchanging the sums, and noting that $j$ is never in the tree of $i$, gives the right
side of (3). (1) If $y(B)=1$, every $c_v$ with $v\in B$ vanishes by the column sums, and (3) gives
$\kappa_i(B)=\kappa_j(B)$.

## Depends on

- [Rédei's $g$ from the bits](redei-g.md)
- [The Laplacian of a family of bits](../forests/laplacian.md)
- [Forests on a finite set](../forests/forests.md)
- [Minors over $\mathbb F_2$ as permanents](../forests/permanent-minors.md)

## Proof depends on

- [The forest lemma (Lemma 2.1)](../forests/forest-lemma.md)
- [Rank-one updates and bordered determinants](../forests/rank-one-updates.md)
- [Row operations on minors over $\mathbb F_2$](../forests/row-operations.md)

## Sources

- [Lemma 2.2](../../../sources/rank-5b-locators.md#lemma-22)
