---
article_id: af_69432db87413513c66c26114
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.Rank.CertifiedRankRk
---

# The certified rank hypothesis in positive-rank form

The hypothesis CR₃^Rk is the following assertion. Let $d$ be a squarefree positive integer with
$d\equiv5\pmod8$. Suppose that the 2-Selmer group $\mathrm{Sel}_2(C_d)$ has exactly $8$ elements and
contains a pair $(a,b)$ with $|a|\equiv7\pmod8$. Then $C_d(\mathbb Q)$ has a point of infinite
order.

The premises are those of [CR₃^Sel](../selmer/certified-rank-sel.md); only the conclusion changes,
from "every Selmer class comes from a rational point" to $\operatorname{rank}C_d(\mathbb Q)\ge1$,
which is what the theorems below conclude. It rests on:

- for this 2-adic shape, Tian–Yuan–Zhang (Theorem 3.5 and the argument of the proof of Theorem
  3.5(2), as completed in nt-tyz §4 by Proposition N, which is not refereed), which gives that
  $L(C_d,s)$ vanishes to order exactly one at $s=1$, and Gross–Zagier over an auxiliary imaginary
  quadratic field (Bump–Friedberg–Hoffstein), which gives $\operatorname{rank}C_d(\mathbb Q)\ge1$.
  Their hypothesis, an odd genus sum of class numbers, follows from the premises of CR₃^Rk by
  Corollary 4.4, Theorem 3.6 and Rédei's formula;
- as an alternative that is not needed, Kriz's 2-converse theorem (Theorem 10.13, a preprint whose publication status
  was not checked) for $C_d$ at $p=2$, whose standing assumption holds since $d\ge21$ (by Proposition 0,
  as in [CR₃^Sel](../selmer/certified-rank-sel.md)), together with the corank lemma (the
  Cassels–Tate pairing on $Ш/Ш_{\rm div}$ is nondegenerate and alternating, so
  $\dim(Ш/Ш_{\rm div})[2]$ is even, with no finiteness of $Ш$ assumed), giving
  $\operatorname{rank}C_d(\mathbb Q)=1$.

Neither rank theorem is proved here, so CR₃^Rk is a hypothesis. With Mordell–Weil for $C_d$ it
implies CR₃^Sel, by RK9.

## Depends on

- [The 2-Selmer group of a congruent number curve](../selmer/selmer-group.md)

## Sources

- [The positive-rank form](../../sources/rank-locators.md#the-positive-rank-form)
- [The trust statement for CR3](../../sources/route-k-locators.md#the-trust-statement-for-cr3)
- [Tian-Yuan-Zhang](../../sources/rank-locators.md#tian-yuan-zhang)
- [Proposition N](../../sources/rank-5b-locators.md#proposition-n)
- [Gross-Zagier](../../sources/rank-locators.md#gross-zagier)
- [Kriz](../../sources/rank-locators.md#kriz)
- [Cassels-Tate](../../sources/route-k-locators.md#cassels-tate)
