---
article_id: af_5012b9f3eb6f702d0b769d18
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.certifiedRank5b_of_certifiedRankTYZ
---

# CR₃^TYZ implies CR₃^5b

Assume the certified rank hypothesis in Tian–Yuan–Zhang form CR₃^TYZ. Then the certified rank
hypothesis in row-5b form CR₃^5b holds: for every squarefree $n\equiv5\pmod8$ with
$|\mathrm{Sel}_2(C_n)|=8$ and $\det M_{5b}=1$, every 2-Selmer class of $C_n$ comes from a rational
point.

**Proof sketch.** Under the hypotheses of CR₃^5b, Theorem 3.6 gives
$T_{5b}(n)=\det M_{5b}=1$, and CR₃^TYZ applies.

## Depends on

- [The certified rank hypothesis in Tian–Yuan–Zhang form](certified-rank-tyz.md)
- [The certified rank hypothesis in row-5b form](certified-rank-5b.md)

## Proof depends on

- [Row 5b of Smith's table (Theorem 3.6)](genus-sum/theorem-3-6.md)

## Sources

- [The hypothesis in Tian-Yuan-Zhang form](../../sources/rank-5b-locators.md#the-hypothesis-in-tian-yuan-zhang-form)
- [Theorem 3.6](../../sources/rank-5b-locators.md#theorem-36)
