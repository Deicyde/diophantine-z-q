---
article_id: af_15d073ffd5dcd043f444bbdb
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank.certifiedRankInf_iff_certifiedRankRk, ZInQ.RouteK.Rank.certifiedRankTYZInf_iff_certifiedRankTYZRk, ZInQ.RouteK.Rank.certifiedRankTYZClInf_iff_certifiedRankTYZClRk, ZInQ.RouteK.Rank.certifiedRankDLInf_iff_certifiedRankDLRk
---

# The infinitely-many-points forms are equivalent to the positive-rank forms

The hypotheses CR₃^Inf and CR₃^Rk are equivalent. Likewise CR₃^TYZ,Inf is equivalent to CR₃^TYZ,Rk,
CR₃^TYZ_Cl,Inf to CR₃^TYZ_Cl,Rk, and CR₃^DL,Inf to CR₃^DL,Rk.

**Proof sketch.** In each pair the two hypotheses have the same premises and differ only in the
conclusion, so it suffices to compare the conclusions for each fixed value of the data. For
CR₃^Inf, CR₃^TYZ,Inf and CR₃^TYZ_Cl,Inf, fix $d$ with $d\equiv5\pmod8$; then $d\ne0$, and by
[the equivalence of infinite order and infinitely many points](infinite-order-iff.md),
$C_d(\mathbb Q)$ has a point of infinite order exactly when $y^2=x^3-d^2x$ has infinitely many
rational solutions. For CR₃^DL,Inf, fix $\beta,\theta,p_0$ satisfying the premises and a choice of
slot data. By [the realization](../../route-k/realization.md), $d_1\equiv5\pmod8$, and
$d_1|\theta|\equiv5\pmod8$ as well (as in [CR₃^DL,Rk from CR₃^Rk](../two-curves/certified-rank-dl-rk-of-rk.md)),
so both are nonzero and the same equivalence applies to each of the two curves.

## Depends on

- [The certified rank hypothesis in infinitely-many-points form](certified-rank-inf.md)
- [The Tian–Yuan–Zhang hypothesis in infinitely-many-points form](certified-rank-tyz-inf.md)
- [The class-number hypothesis in infinitely-many-points form](certified-rank-tyz-cl-inf.md)
- [The infinitely-many-points hypothesis on the two curves of a slot choice](certified-rank-dl-inf.md)
- [The certified rank hypothesis in positive-rank form](../certified-rank-rk.md)
- [The Tian–Yuan–Zhang hypothesis in positive-rank form](../certified-rank-tyz-rk.md)
- [The class-number hypothesis in positive-rank form](../certified-rank-tyz-cl-rk.md)
- [The positive-rank hypothesis on the two curves of a slot choice](../two-curves/certified-rank-dl-rk.md)

## Proof depends on

- [A point of infinite order exists iff there are infinitely many rational points](infinite-order-iff.md)
- [The realization: both curves reduce to the base configuration](../../route-k/realization.md)
- [CR₃^DL,Rk from CR₃^Rk](../two-curves/certified-rank-dl-rk-of-rk.md)
- [CR₃^Sel from CR₃^Rk](../certified-rank-sel-of-rk.md)

## Sources

- [The infinitely-many-points forms](../../../sources/rank-locators.md#the-infinitely-many-points-forms)
