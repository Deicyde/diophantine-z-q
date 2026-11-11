---
article_id: af_155f60e374e9c7ca4219f799
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.certifiedRankTYZ_iff', ZInQ.RouteK.Rank5b.certifiedRankTYZ_iff_of_redeiFormula, ZInQ.RouteK.Redei.certifiedRankTYZ_iff_of_oddGClStatement
---

# CR₃ with class numbers is CR₃^TYZ

The hypothesis CR₃^TYZ_Cl, stated with Tian, Yuan and Zhang's genus class numbers $g(d_B)$, holds
if and only if the hypothesis CR₃^TYZ, stated with Rédei's $g_d(B)$, holds. Along the way, the
same equivalence is proved from Rédei's formula taken as an assumption, and from the 4-rank
statement taken as an assumption.

**Proof sketch.** The two hypotheses have the same premises and conclusion except for their genus
sums: CR₃^TYZ_Cl asks $T^{\rm Cl}_{5b}(d)=1$ where CR₃^TYZ asks $T_{5b}(d)=1$, for squarefree
$d\equiv5\pmod8$. Such $d$ is odd, so under Rédei's formula the two genus sums agree, and the two
hypotheses are equivalent. The 4-rank statement implies Rédei's formula, which gives the second
conditional form. Since [Rédei's formula](redei-formula.md) holds, the two hypotheses are
equivalent.

## Depends on

- [The certified rank hypothesis with class numbers](certified-rank-tyz-cl.md)
- [The certified rank hypothesis in Tian–Yuan–Zhang form](../rank-5b/certified-rank-tyz.md)
- [The statement of Rédei's formula](redei-formula-statement.md)
- [The 4-rank statement](four-rank/four-rank-statement.md)

## Proof depends on

- [The genus sum of class numbers is the genus sum of Rédei bits](genus-sums-agree.md)
- [Rédei's formula](redei-formula.md)
- [Rédei's formula from the 4-rank statement](bits/formula-from-four-rank.md)

## Sources

- [The hypothesis in class-number form](../../sources/redei-locators.md#the-hypothesis-in-class-number-form)
