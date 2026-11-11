---
article_id: af_14de3402fad9780ec021699d
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.Rank.CertifiedRankTYZClRk
---

# The class-number hypothesis in positive-rank form

The hypothesis CR₃^TYZ_Cl,Rk is the following assertion. Let $d$ be a squarefree positive integer
with $d\equiv5\pmod8$ whose genus sum of class numbers
$$T^{\mathrm{Cl}}_{5b}(d)=\sum_\pi\prod_{B\in\pi}\#\bigl(2\,\mathrm{Cl}(\mathbb Q(\sqrt{-d_B}))\bigr)\pmod 2$$
is $1$. Here $\pi$ runs over the set partitions of the primes of $d$ with exactly one block with
$d_B\equiv7$, exactly one with $d_B\equiv3$, and all other blocks with $d_B\equiv1\pmod8$; $d_B$ is
the product of the primes in $B$, and $2\,\mathrm{Cl}(K)$ is the subgroup of squares of the class
group of the ring of integers of $K$. Then $C_d(\mathbb Q)$ has a point of infinite order.

This is Tian–Yuan–Zhang with their own genus class numbers (Theorem 3.5 and the argument of the
proof of Theorem 3.5(2), as completed in nt-tyz §4, Proposition N), which gives that $L(C_d,s)$
vanishes to order exactly one at $s=1$, followed by Gross–Zagier, which gives
$\operatorname{rank}C_d(\mathbb Q)\ge1$. No Rédei formula and no condition on $\mathrm{Sel}_2(C_d)$
enter. It is a hypothesis, not proved here.

## Depends on

- [The genus sum of class numbers](../redei/class-number-genus-sum.md)

## Sources

- [The positive-rank form](../../sources/rank-locators.md#the-positive-rank-form)
- [Tian-Yuan-Zhang](../../sources/rank-locators.md#tian-yuan-zhang)
- [Gross-Zagier](../../sources/rank-locators.md#gross-zagier)
