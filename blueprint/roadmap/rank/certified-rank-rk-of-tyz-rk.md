---
article_id: af_6c58b48f45670fbca0d6e4c7
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank.certifiedRankRk_of_certifiedRankTYZRk
---

# CR₃^TYZ,Rk implies CR₃^Rk

The hypothesis CR₃^TYZ,Rk implies CR₃^Rk.

**Proof sketch.** Let $d\equiv5\pmod8$ be a squarefree positive integer with
$|\mathrm{Sel}_2(C_d)|=8$ and a pair $(a,b)\in\mathrm{Sel}_2(C_d)$ with $|a|\equiv7\pmod8$.
Corollary 4.4 gives $\det M_{5b}=1$, and Theorem 3.6 gives $\det M_{5b}=T_{5b}(d)$, so
$T_{5b}(d)=1$. CR₃^TYZ,Rk then gives a point of infinite order on $C_d$.

## Depends on

- [The certified rank hypothesis in positive-rank form](certified-rank-rk.md)
- [The Tian–Yuan–Zhang hypothesis in positive-rank form](certified-rank-tyz-rk.md)

## Proof depends on

- [A first coordinate congruent to 7 forces $\det M_{5b}=1$ (Corollary 4.4)](../rank-5b/corollary-4-4.md)
- [Row 5b of Smith's table (Theorem 3.6)](../rank-5b/genus-sum/theorem-3-6.md)

## Sources

- [Row 5b and Rédei](../../sources/rank-locators.md#row-5b-and-redei)
- [Corollary 4.4](../../sources/rank-5b-locators.md#corollary-44)
