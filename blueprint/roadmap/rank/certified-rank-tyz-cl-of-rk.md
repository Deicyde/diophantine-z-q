---
article_id: af_2b53d2f10e114ee82b541381
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank.certifiedRankTYZCl_of_certifiedRankTYZClRk', ZInQ.RouteK.Rank.certifiedRankTYZCl_of_certifiedRankTYZClRk
---

# CR₃^TYZ_Cl from CR₃^TYZ_Cl,Rk

The hypothesis CR₃^TYZ_Cl,Rk implies the class-number form CR₃^TYZ_Cl of the certified rank
hypothesis.

Along the way: CR₃^TYZ_Cl,Rk implies CR₃^TYZ_Cl under the assumption that $C_d(\mathbb Q)$ is
finitely generated for every natural number $d\ne0$.

**Proof sketch.** First under the assumption. Let $d\equiv5\pmod8$ be a squarefree positive integer
with $|\mathrm{Sel}_2(C_d)|=8$ and $T^{\mathrm{Cl}}_{5b}(d)=1$. Then $d\ne0$, so $C_d(\mathbb Q)$ is
finitely generated, and CR₃^TYZ_Cl,Rk gives a point of infinite order on $C_d$. RK9, with
$|\mathrm{Sel}_2(C_d)|=8$, makes the x-form of the covering of every Selmer class hold over
$\mathbb Q$, which is the conclusion of CR₃^TYZ_Cl. Mordell–Weil for the congruent number curves
supplies the assumption, which gives the implication without it.

## Depends on

- [The class-number hypothesis in positive-rank form](certified-rank-tyz-cl-rk.md)
- [The certified rank hypothesis with class numbers](../redei/certified-rank-tyz-cl.md)

## Proof depends on

- [Positive rank and a Selmer group of order eight give every Selmer class (RK9)](two-descent/every-selmer-class.md)
- [Mordell–Weil for the congruent number curves](mordell-weil/finite-generation.md)
- [CR₃^Sel from CR₃^Rk](certified-rank-sel-of-rk.md)

## Sources

- [RK9](../../sources/rank-locators.md#rk9)
- [Mordell-Weil for the congruent number curves](../../sources/rank-locators.md#mordell-weil-for-the-congruent-number-curves)
