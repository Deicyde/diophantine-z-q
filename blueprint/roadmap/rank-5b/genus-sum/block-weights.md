---
article_id: af_8912c09f488ff95b18acda3a
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.w1_eq, ZInQ.RouteK.Rank5b.Sec3.w7_eq, ZInQ.RouteK.Rank5b.Sec3.w3_eq, ZInQ.RouteK.Rank5b.Sec3.w7, ZInQ.RouteK.Rank5b.Sec3.w3, ZInQ.RouteK.Rank5b.Sec3.w1, ZInQ.RouteK.Rank5b.Sec3.treeY, ZInQ.RouteK.Rank5b.Sec3.blockH, ZInQ.RouteK.Rank5b.Sec3.sum_blockH, ZInQ.RouteK.Rank5b.Sec3.treeY_single, ZInQ.RouteK.Rank5b.Sec3.sum_kappa_eq_allF, ZInQ.RouteK.Rank5b.Sec3.sum_powerset_card_one, ZInQ.RouteK.Rank5b.Sec3.sum_powerset_card_eq, ZInQ.RouteK.Rank5b.Sec3.sum_offDiag_eq, ZInQ.RouteK.Rank5b.Sec3.sum_offDiag_eq_erase, ZInQ.RouteK.Rank5b.Sec3.zmod2_cases
---

# Block weights as forest sums

Let $a,y,z$ be bits on a finite set $V$ that satisfy reciprocity, and let $B\subseteq V$. Let
$w_7(B)$, $w_3(B)$ and $w_1(B)$ be $g(B)$ if $B$ has class $7$, $3$, respectively $1$, and $0$
otherwise. For a forest $f$ on $B$ with root set $S\subseteq B$ put
$$Y(f)=\prod_{\rho\in S}y(T_\rho),$$
the product of the sums of $y$ over its trees $T_\rho=\{v\in B:\text{the root of }v\text{ is }\rho\}$,
and let $\mathrm{wt}(f)=\mathrm{wt}_{B\setminus S}(f)$. Then
$$w_7(B)=\sum_{f\text{ with one root }\rho}(y_\rho+z_\rho)\,\mathrm{wt}(f)\,Y(f),\qquad
w_3(B)=\sum_{f\text{ with one root }\rho}z_\rho\,\mathrm{wt}(f)\,Y(f),$$
$$w_1(B)=\sum_{f\text{ with two roots }i,j}z_iz_j\,\mathrm{wt}(f)\,Y(f),$$
the sums over the forests $f$ on $B$ with exactly one, respectively exactly two, roots in $B$.

Along the way: grouping the forests on $B$ by their root sets, a sum over the forests with $k$ roots
of $e(S)\,\mathrm{wt}(f)\,Y(f)$ is $\sum_{S\subseteq B,|S|=k}e(S)\sum_{f\text{ rooted at }S}\mathrm{wt}(f)\,Y(f)$;
a forest with the single root $\rho$ has $Y(f)=y(B)$; and for any $e_\rho\in\mathbb F_2$,
$\sum_{\rho\in B}e_\rho\,y(B)\,\kappa_\rho(B)=\sum_{f\text{ with one root }\rho}e_\rho\,\mathrm{wt}(f)\,Y(f)$.

**Proof sketch.** *Classes 7 and 3.* By the forest count of the cofactors in Lemma 2.2, $\kappa_\rho(B)$ is the sum of $\mathrm{wt}(f)$ over
the forests on $B$ with the single root $\rho$, and for these $Y(f)=y(B)$. So the right sides are
$\sum_\rho(y_\rho+z_\rho)\,y(B)\,\kappa_\rho(B)$ and $\sum_\rho z_\rho\,y(B)\,\kappa_\rho(B)$. If $y(B)=0$,
both sides vanish. If $y(B)=1$, (2.1) turns them into $(1+z(B))\,g(B)$ and $z(B)\,g(B)$, which are
$w_7(B)$ and $w_3(B)$.

*Class 1.* By (2.2) and a check of the two values of $y(B)$,
$w_1(B)=(1+y(B))(1+z(B))\sum_\rho z_\rho\kappa_\rho(B)$. Since $z_\rho(1+z_\rho)=0$,
$(1+z(B))\sum_\rho z_\rho\kappa_\rho(B)$ is the sum over the ordered pairs $\rho\ne j$ in $B$ of
$z_\rho z_j\kappa_\rho(B)$, that is, the sum over the two-element sets $\{i,j\}\subseteq B$ of
$z_iz_j(\kappa_i(B)+\kappa_j(B))$. By Lemma 2.2(3) this is
$z_iz_j\sum_\varphi\mathrm{wt}(\varphi)\sum_{v\in T_i}c_v$ over the forests $\varphi$ rooted at $\{i,j\}$, and
by the column sums of Lemma 2.2, $\sum_{v\in T_i}c_v=y(T_i)(1+y(B))$. As $B$ is the union of the two trees,
$y(B)=y(T_i)+y(T_j)$, hence $(1+y(B))\,y(T_i)(1+y(B))=y(T_i)(1+y(T_i)+y(T_j))=y(T_i)\,y(T_j)=Y(\varphi)$.
Grouping the forests with two roots by their root sets gives the formula for $w_1(B)$.

## Depends on

- [The genus sum $T_{5b}$](genus-sum.md)
- [Rédei's $g$ from the bits](redei-g.md)
- [Forests on a finite set](../forests/forests.md)

## Proof depends on

- [The cofactors of the Laplacian (Lemma 2.2)](lemma-2-2.md)
- [Rédei's $g$ through the cofactors (2.1), (2.2)](redei-g-cofactors.md)

## Sources

- [Lemma 2.2](../../../sources/rank-5b-locators.md#lemma-22)
- [Proposition 2.3](../../../sources/rank-5b-locators.md#proposition-23)
- [Proposition 3.5](../../../sources/rank-5b-locators.md#proposition-35)
- [Propositions 3.3 and 3.4](../../../sources/rank-5b-locators.md#propositions-33-and-34)
