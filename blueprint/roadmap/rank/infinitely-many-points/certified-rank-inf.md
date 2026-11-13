---
article_id: af_caf88329a2d903d0eae64269
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.Rank.CertifiedRankInf
---

# The certified rank hypothesis in infinitely-many-points form

The hypothesis CR₃^Inf is the following assertion. Let $d$ be a squarefree positive integer with
$d\equiv5\pmod8$. Suppose that the 2-Selmer group $\mathrm{Sel}_2(C_d)$ has exactly $8$ elements and
contains a pair $(a,b)$ with $|a|\equiv7\pmod8$. Then $y^2=x^3-d^2x$ has infinitely many rational
solutions $(x,y)\in\mathbb Q^2$.

The premises are those of [CR₃^Rk](../certified-rank-rk.md); only the conclusion changes, from "a
point of infinite order on $C_d(\mathbb Q)$" to "infinitely many rational solutions", which mentions
no group law. The two hypotheses are equivalent, so CR₃^Inf rests on the same theorems:
Tian–Yuan–Zhang as completed by Proposition N, which is not refereed, and Gross–Zagier with an
auxiliary field. None of them is
proved here, so CR₃^Inf is a hypothesis.

**Remark (classical meaning).** For the squarefree $d$ here, infinitely many rational solutions is
the classical statement that $d$ is a congruent number. This is not part of the hypothesis and is
not used.

## Depends on

- [The 2-Selmer group of a congruent number curve](../../selmer/selmer-group.md)
- [Infinitely many rational solutions of $y^2=x^3-d^2x$](infinitely-many-points.md)

## Sources

- [The infinitely-many-points forms](../../../sources/rank-locators.md#the-infinitely-many-points-forms)
- [The positive-rank form](../../../sources/rank-locators.md#the-positive-rank-form)
- [Tian-Yuan-Zhang](../../../sources/rank-locators.md#tian-yuan-zhang)
- [Gross-Zagier](../../../sources/rank-locators.md#gross-zagier)
- [The trust statement for CR3](../../../sources/route-k-locators.md#the-trust-statement-for-cr3)
