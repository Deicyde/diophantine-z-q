---
article_id: af_1d54d5a58795ae4f9efb72ed
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank.certifiedRankTYZ_of_certifiedRankTYZRk', ZInQ.RouteK.Rank.certifiedRankTYZ_of_certifiedRankTYZRk
---

# CR₃^TYZ from CR₃^TYZ,Rk

The hypothesis CR₃^TYZ,Rk implies the Tian–Yuan–Zhang form CR₃^TYZ of the certified rank
hypothesis.

Along the way: CR₃^TYZ,Rk implies CR₃^TYZ under the assumption that $C_d(\mathbb Q)$ is finitely
generated for every natural number $d\ne0$.

**Proof sketch.** First under the assumption. Let $d\equiv5\pmod8$ be a squarefree positive integer
with $|\mathrm{Sel}_2(C_d)|=8$ and $T_{5b}(d)=1$. Then $d\ne0$, so $C_d(\mathbb Q)$ is finitely
generated, and CR₃^TYZ,Rk gives a point of infinite order on $C_d$. RK9, with
$|\mathrm{Sel}_2(C_d)|=8$, makes the x-form of the covering of every Selmer class hold over
$\mathbb Q$, which is the conclusion of CR₃^TYZ. Mordell–Weil for the congruent number curves
supplies the assumption, which gives the implication without it.

## Depends on

- [The Tian–Yuan–Zhang hypothesis in positive-rank form](certified-rank-tyz-rk.md)
- [The certified rank hypothesis in Tian–Yuan–Zhang form](../rank-5b/certified-rank-tyz.md)

## Proof depends on

- [Positive rank and a Selmer group of order eight give every Selmer class (RK9)](two-descent/every-selmer-class.md)
- [Mordell–Weil for the congruent number curves](mordell-weil/finite-generation.md)
- [CR₃^Sel from CR₃^Rk](certified-rank-sel-of-rk.md)

## Sources

- [RK9](../../sources/rank-locators.md#rk9)
- [Mordell-Weil for the congruent number curves](../../sources/rank-locators.md#mordell-weil-for-the-congruent-number-curves)
