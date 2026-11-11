---
article_id: af_4f94fd6ebf1dd6ec9805e722
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.sum_class1_eq_sum_class3, ZInQ.RouteK.Rank5b.Sec3.sum_class1_eq_forest
---

# From class-1 blocks to class-3 blocks (Proposition 3.5)

Let $a,y,z$ be bits on a finite set $V$ that satisfy reciprocity and $y(V)=0$. Then
$$\sum_{\pi\text{ into blocks of class }1}\ \prod_{B\in\pi}g(B)\;=\;\sum_{\pi\text{ into blocks of class }3}\ \prod_{B\in\pi}g(B),$$
both sums over set partitions of $V$.

Along the way, under reciprocity alone,
$$\sum_{\pi\text{ into blocks of class }1}\ \prod_{B\in\pi}g(B)=\sum_f\,p(R)\,z^R\,\mathrm{wt}(f)\prod_{\rho\in R}y(T_\rho),$$
the sum over the forests $f$ on $V$ with root set $R$, where $p(R)$ is the number of
fixed-point-free involutions of $R$.

**Proof sketch.** Write $w_1(B)$ as the sum over the forests on $B$ with two roots $i,j$ of
$z_iz_j\,\mathrm{wt}(h)\,Y(h)$, and glue along the partition. As in Proposition 3.3, the class-1
partition sum becomes $\sum_fN_2(f)\,z^R\,\mathrm{wt}(f)\prod_\rho y(T_\rho)$, with $N_2(f)$ the number of
compatible partitions in which every block holds exactly two roots; by the count with $E=\emptyset$,
$N_2(f)=p(R)$. By Proposition 3.3 the class-3 partition sum is
$\sum_fz^R\,\mathrm{wt}(f)\prod_\rho y(T_\rho)$. Compare the coefficients forest by forest. If
$\prod_\rho y(T_\rho)\ne0$, every tree has $y(T_\rho)=1$, so $|R|\equiv y(V)=0\pmod2$, and the number of
pairings of a set of even size is odd; so $p(R)$ is odd and the coefficients agree in $\mathbb F_2$.

## Depends on

- [The genus sum $T_{5b}$](genus-sum.md)
- [Forests on a finite set](../forests/forests.md)
- [Block weights as forest sums](block-weights.md)
- [Pairings are odd in number exactly on sets of even size](../forests/pairings.md)

## Proof depends on

- [$\det M_1$ as a sum over partitions into class-3 blocks (Proposition 3.3)](proposition-3-3.md)
- [The genus sum as a forest sum](genus-sum-forests.md)
- [Compatible partitions with one or two roots per block](roots-per-block.md)

## Sources

- [Proposition 3.5](../../../sources/rank-5b-locators.md#proposition-35)
