---
article_id: af_413101c7c48f788cedb3c6d9
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.Rank.CertifiedRankTYZRk
---

# The Tian–Yuan–Zhang hypothesis in positive-rank form

The hypothesis CR₃^TYZ,Rk is the following assertion. Let $d$ be a squarefree positive integer with
$d\equiv5\pmod8$ whose genus sum of row 5b, built from Rédei's bits, is odd: $T_{5b}(d)=1$. Then
$C_d(\mathbb Q)$ has a point of infinite order.

No condition on $\mathrm{Sel}_2(C_d)$ enters. It rests on Tian–Yuan–Zhang (Theorem 3.5 and the
argument of the proof of Theorem 3.5(2), as completed in nt-tyz §4, Proposition N), which gives
that $L(C_d,s)$ vanishes to order exactly one at $s=1$, followed by Gross–Zagier with an auxiliary
imaginary quadratic field, which gives $\operatorname{rank}C_d(\mathbb Q)\ge1$. Rédei's formula
identifies $T_{5b}(d)$ with Tian, Yuan and Zhang's genus sum of class numbers. The deep theorems are
not proved here, so CR₃^TYZ,Rk is a hypothesis. It is the
[Tian–Yuan–Zhang form CR₃^TYZ](../rank-5b/certified-rank-tyz.md) with the premise
$|\mathrm{Sel}_2(C_d)|=8$ dropped and the conclusion replaced by positive rank.

## Depends on

- [The genus sum $T_{5b}$](../rank-5b/genus-sum/genus-sum.md)

## Sources

- [The positive-rank form](../../sources/rank-locators.md#the-positive-rank-form)
- [Tian-Yuan-Zhang](../../sources/rank-locators.md#tian-yuan-zhang)
- [Gross-Zagier](../../sources/rank-locators.md#gross-zagier)
- [Row 5b and Rédei](../../sources/rank-locators.md#row-5b-and-redei)
