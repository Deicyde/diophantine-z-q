---
article_id: af_b76dd137efac4979aab4632c
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.certifiedRankSel_of_certifiedRank5b
---

# CR₃^5b implies CR₃^Sel

Assume the certified rank hypothesis in row-5b form CR₃^5b. Then the certified rank
hypothesis in Selmer form CR₃^Sel holds: for every squarefree $n>0$ with $n\equiv5\pmod8$ and
$|\mathrm{Sel}_2(C_n)|=8$ such that some Selmer class has $|a|\equiv7\pmod8$, every Selmer class
of $C_n$ comes from a rational point.

**Proof sketch.** Under the hypotheses of CR₃^Sel, Corollary 4.4 gives $\det M_{5b}=1$, and CR₃^5b
applies.

## Depends on

- [The certified rank hypothesis in row-5b form](certified-rank-5b.md)
- [The certified rank hypothesis in Selmer form](../selmer/certified-rank-sel.md)

## Proof depends on

- [A first coordinate congruent to 7 forces $\det M_{5b}=1$ (Corollary 4.4)](corollary-4-4.md)

## Sources

- [Corollary 4.4](../../sources/rank-5b-locators.md#corollary-44)
