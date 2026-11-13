---
article_id: af_c51db40665d14fe5b0898b9a
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank.certifiedRank_of_certifiedRankRk', ZInQ.RouteK.Rank.certifiedRank_of_certifiedRankRk
---

# CR₃ from CR₃^Rk

The hypothesis CR₃^Rk implies the certified rank hypothesis CR₃.

Along the way: CR₃^Rk implies CR₃ under the assumption that $C_d(\mathbb Q)$ is finitely generated
for every natural number $d\ne0$.

**Proof sketch.** Under the assumption, CR₃^Rk gives CR₃^Sel by RK9, and CR₃^Sel implies CR₃
through Proposition 0. Mordell–Weil for the congruent number curves supplies the assumption, which
gives the implication without it.

## Depends on

- [The certified rank hypothesis in positive-rank form](certified-rank-rk.md)
- [The certified rank hypothesis](../main/certified-rank.md)

## Proof depends on

- [CR₃^Sel from CR₃^Rk](certified-rank-sel-of-rk.md)
- [The certified rank hypothesis from its Selmer form](../selmer/certified-rank-of-sel.md)
- [Mordell–Weil for the congruent number curves](mordell-weil/finite-generation.md)

## Sources

- [RK9](../../sources/rank-locators.md#rk9)
- [Mordell-Weil for the congruent number curves](../../sources/rank-locators.md#mordell-weil-for-the-congruent-number-curves)
- [The hypothesis in the literature's form](../../sources/selmer-locators.md#the-hypothesis-in-the-literatures-form)
