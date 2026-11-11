---
article_id: af_5437e80e0ce471523d91b094
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.det_Pmat, ZInQ.RouteK.Rank5b.Sec3.Pmat, ZInQ.RouteK.Rank5b.Sec3.card_eq_of_isTransv, ZInQ.RouteK.Rank5b.Sec3.sum_transv, ZInQ.RouteK.Rank5b.Sec3.sum_powerset_sum
---

# The determinant of $P(c,d)$ as a forest sum

Let $a$ be bits on a finite set $V$, $L=L_V$ their Laplacian, and $c,d\in\mathbb F_2^V$, with
diagonal matrices $D_c$, $D_d$. Let $P(c,d)$ be the symmetric $(V\sqcup V)$-square matrix
$$P(c,d)=\begin{pmatrix}D_d&L^{\mathsf T}\\L&D_c\end{pmatrix}.$$
Then
$$\det P(c,d)=\sum_{F\subseteq V}c^F\sum_f\mathrm{wt}(f)\prod_{\rho\in F}d(T_\rho),$$
the inner sum over the forests $f$ on $V$ rooted at $F$, where $c^F=\prod_{\rho\in F}c_\rho$,
$T_\rho$ is the tree of $f$ at $\rho$, and $d(T)=\sum_{v\in T}d_v$.

**Proof sketch.** By the permanent form of principal minors, $\det P(c,d)$ is the permanent of
$P(c,d)$ on all of $V\sqcup V$. Write $P(c,d)=Q+D$ with
$Q=\begin{pmatrix}0&L^{\mathsf T}\\L&0\end{pmatrix}$ and $D$ diagonal with diagonal $e=(d,c)$.
The expansion of a diagonal shift gives
$\operatorname{per}(Q+D)=\sum_Se^S\operatorname{per}Q[S^c,S^c]$, over the subsets $S$ of $V\sqcup V$.
Write $S=W\sqcup F$, so that $e^S=d^Wc^F$ and $S^c=(V\setminus W)\sqcup(V\setminus F)$.
By the anti-diagonal block rule,
$$\operatorname{per}Q[S^c,S^c]=\operatorname{per}L^{\mathsf T}[V\setminus W,V\setminus F]\cdot
\operatorname{per}L[V\setminus F,V\setminus W]=\operatorname{per}L[V\setminus F,V\setminus W]^2
=\operatorname{per}L[V\setminus F,V\setminus W],$$
using the transpose rule and $t^2=t$ in $\mathbb F_2$. If $|F|\ne|W|$, this minor is $0$, and $W$
is a transversal of no forest rooted at $F$, since a transversal has one point in each of the $|F|$
trees. If $|F|=|W|$, the forest lemma for $U=V$ makes it the sum of $\mathrm{wt}(f)$ over the
forests $f$ rooted at $F$ of which $W$ is a transversal. Exchanging the sums, a forest rooted at
$F$ carries $c^F\mathrm{wt}(f)\sum_Wd^W$ over its transversals $W$. A transversal is a choice of
one point in each tree, so $\sum_Wd^W=\prod_{\rho\in F}d(T_\rho)$.

## Depends on

- [Forests on a finite set](forests.md)
- [The Laplacian of a family of bits](laplacian.md)

## Proof depends on

- [Minors over $\mathbb F_2$ as permanents](permanent-minors.md)
- [Minors of anti-diagonal block matrices and of diagonal shifts](block-minors.md)
- [Rank-one updates and bordered determinants](rank-one-updates.md)
- [The forest lemma (Lemma 2.1)](forest-lemma.md)

## Sources

- [Propositions 3.3 and 3.4](../../../sources/rank-5b-locators.md#propositions-33-and-34)
