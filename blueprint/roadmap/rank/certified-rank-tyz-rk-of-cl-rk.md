---
article_id: af_eaec6c44ec66c40079c070d8
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.certifiedRankTYZRk_of_certifiedRankTYZClRk, ZInQ.RouteK.Redei.certifiedRankTYZRk_of_oddGClStatement
---

# CR₃^TYZ_Cl,Rk implies CR₃^TYZ,Rk

The hypothesis CR₃^TYZ_Cl,Rk implies CR₃^TYZ,Rk: if every squarefree positive $d\equiv5\pmod8$ with
$T^{\mathrm{Cl}}_{5b}(d)=1$ has a point of infinite order on $C_d$, then so does every squarefree
positive $d\equiv5\pmod8$ with $T_{5b}(d)=1$.

Along the way: the 4-rank statement and CR₃^TYZ_Cl,Rk together give CR₃^TYZ,Rk.

**Proof sketch.** First under the 4-rank statement. It gives Rédei's formula. Let
$d\equiv5\pmod8$ be squarefree with $T_{5b}(d)=1$. Then $d$ is odd, so the two genus sums agree,
$T^{\mathrm{Cl}}_{5b}(d)=T_{5b}(d)=1$, and CR₃^TYZ_Cl,Rk gives a point of infinite order on $C_d$.
The 4-rank statement holds by Rédei's theorem, which gives the implication without assumption.

## Depends on

- [The Tian–Yuan–Zhang hypothesis in positive-rank form](certified-rank-tyz-rk.md)
- [The class-number hypothesis in positive-rank form](certified-rank-tyz-cl-rk.md)
- [The 4-rank statement](../redei/four-rank/four-rank-statement.md)

## Proof depends on

- [Rédei's theorem on the 4-rank](../redei/four-rank/redei-theorem.md)
- [Rédei's formula from the 4-rank statement](../redei/bits/formula-from-four-rank.md)
- [The genus sum of class numbers is the genus sum of Rédei bits](../redei/genus-sums-agree.md)

## Sources

- [Step 8: the bridge](../../sources/redei-locators.md#step-8-the-bridge)
- [Row 5b and Rédei](../../sources/rank-locators.md#row-5b-and-redei)
