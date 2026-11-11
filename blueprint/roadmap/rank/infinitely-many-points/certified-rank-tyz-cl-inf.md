---
article_id: af_a71ce55b25a4b0705492e713
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.Rank.CertifiedRankTYZClInf
---

# The class-number hypothesis in infinitely-many-points form

The hypothesis CR₃^TYZ_Cl,Inf is the following assertion. Let $d$ be a squarefree positive integer
with $d\equiv5\pmod8$ whose genus sum of class numbers
$$T^{\mathrm{Cl}}_{5b}(d)=\sum_\pi\prod_{B\in\pi}\#\bigl(2\,\mathrm{Cl}(\mathbb Q(\sqrt{-d_B}))\bigr)\pmod 2$$
is $1$. Here $\pi$ runs over the set partitions of the primes of $d$ with exactly one block with
$d_B\equiv7$, exactly one with $d_B\equiv3$, and all other blocks with $d_B\equiv1\pmod8$; $d_B$ is
the product of the primes in $B$, and $2\,\mathrm{Cl}(K)$ is the subgroup of squares of the class
group of the ring of integers of $K$. Then $y^2=x^3-d^2x$ has infinitely many rational solutions
$(x,y)\in\mathbb Q^2$.

The premises are those of [CR₃^TYZ_Cl,Rk](../certified-rank-tyz-cl-rk.md); only the conclusion
changes, from a point of infinite order to infinitely many rational solutions, which mentions no
group law. The two hypotheses are equivalent, so CR₃^TYZ_Cl,Inf rests on Tian–Yuan–Zhang with their
own genus class numbers, as completed by Proposition N, which is not refereed, followed by
Gross–Zagier with an auxiliary field. No Rédei formula and no condition on
$\mathrm{Sel}_2(C_d)$ enter. It is a hypothesis, not proved here.

**Remark (classical meaning).** For the squarefree $d$ here, infinitely many rational solutions is
the classical statement that $d$ is a congruent number. This is not part of the hypothesis and is
not used.

## Depends on

- [The genus sum of class numbers](../../redei/class-number-genus-sum.md)
- [Infinitely many rational solutions of $y^2=x^3-d^2x$](infinitely-many-points.md)

## Sources

- [The infinitely-many-points forms](../../../sources/rank-locators.md#the-infinitely-many-points-forms)
- [The positive-rank form](../../../sources/rank-locators.md#the-positive-rank-form)
- [Tian-Yuan-Zhang](../../../sources/rank-locators.md#tian-yuan-zhang)
- [Gross-Zagier](../../../sources/rank-locators.md#gross-zagier)
- [The trust statement for CR3](../../../sources/route-k-locators.md#the-trust-statement-for-cr3)
