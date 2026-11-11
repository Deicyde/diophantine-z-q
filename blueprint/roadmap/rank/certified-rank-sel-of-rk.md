---
article_id: af_a34adccc91b3ad0dc23af3ad
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank.certifiedRankSel_of_certifiedRankRk', ZInQ.RouteK.Rank.certifiedRankSel_of_certifiedRankRk, ZInQ.RouteK.Rank.ne_zero_of_mod_eight_eq_five
---

# CR₃^Sel from CR₃^Rk

The hypothesis CR₃^Rk implies the Selmer form CR₃^Sel of the certified rank hypothesis.

Along the way: a natural number $d\equiv5\pmod8$ is nonzero; and CR₃^Rk implies CR₃^Sel under the
assumption that $C_d(\mathbb Q)$ is finitely generated for every natural number $d\ne0$.

**Proof sketch.** First under the assumption. Let $d\equiv5\pmod8$ be a squarefree positive integer
with $|\mathrm{Sel}_2(C_d)|=8$ and a pair $(a,b)\in\mathrm{Sel}_2(C_d)$ with $|a|\equiv7\pmod8$.
Then $d\ne0$, so $C_d(\mathbb Q)$ is finitely generated, and CR₃^Rk gives a point of infinite
order. RK9 then makes the x-form of every covering $D_{a',b'}$, $(a',b')\in\mathrm{Sel}_2(C_d)$,
hold over $\mathbb Q$, which is the conclusion of CR₃^Sel. Mordell–Weil for the congruent number
curves supplies the assumption, which gives the implication without it.

## Depends on

- [The certified rank hypothesis in positive-rank form](certified-rank-rk.md)
- [The certified rank hypothesis in Selmer form](../selmer/certified-rank-sel.md)

## Proof depends on

- [Positive rank and a Selmer group of order eight give every Selmer class (RK9)](two-descent/every-selmer-class.md)
- [Mordell–Weil for the congruent number curves](mordell-weil/finite-generation.md)

## Sources

- [RK9](../../sources/rank-locators.md#rk9)
- [Mordell-Weil for the congruent number curves](../../sources/rank-locators.md#mordell-weil-for-the-congruent-number-curves)
