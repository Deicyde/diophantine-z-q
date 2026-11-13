---
article_id: af_755b80700166574c1184f60d
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankInf, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZInf, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClInf, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankDLInf
---

# The main theorem from the infinitely-many-points forms of the rank hypothesis

Assume the minimal height hypothesis and the hypothesis CR₃^Inf. Then the target statement holds,
as in [the main theorem](main-theorem.md). The theorem also holds under the
minimal height hypothesis and CR₃^TYZ,Inf, under the minimal height hypothesis and CR₃^TYZ_Cl,Inf,
and under the minimal height hypothesis and CR₃^DL,Inf.

Each of these hypotheses concludes only that certain equations $y^2=x^3-d^2x$ have infinitely many
rational solutions, a statement that mentions no group law:

- CR₃^Inf: for squarefree positive $d\equiv5\pmod8$, if $|\mathrm{Sel}_2(C_d)|=8$ and some
  $(a,b)\in\mathrm{Sel}_2(C_d)$ has $|a|\equiv7\pmod8$, then $y^2=x^3-d^2x$ has infinitely many
  rational solutions;
- CR₃^TYZ,Inf: for squarefree positive $d\equiv5\pmod8$ with odd genus sum $T_{5b}(d)$ of row 5b,
  $y^2=x^3-d^2x$ has infinitely many rational solutions;
- CR₃^TYZ_Cl,Inf: the same with the genus sum of class numbers $T^{\mathrm{Cl}}_{5b}(d)$ odd;
- CR₃^DL,Inf: for all $\beta,\theta,p_0$ satisfying the hypotheses of the realization, some choice of
  slot data gives $d_1$ such that both $y^2=x^3-d_1^2x$ and $y^2=x^3-(d_1|\theta|)^2x$ have
  infinitely many rational solutions.

Here $C_d$ is the curve $y^2=x^3-d^2x$, whose 2-Selmer group enters the premises of CR₃^Inf.

**Proof sketch.** Each hypothesis is equivalent to its positive-rank form: CR₃^Inf to CR₃^Rk,
CR₃^TYZ,Inf to CR₃^TYZ,Rk, CR₃^TYZ_Cl,Inf to CR₃^TYZ_Cl,Rk, and CR₃^DL,Inf to CR₃^DL,Rk. The first
three cases then follow from
[the main theorem from the positive-rank forms](main-theorem-positive-rank.md), and the last from
[the main theorem from positive rank on the two curves of a slot choice](main-theorem-two-curves.md).

## Depends on

- [The target statement](frozen-target.md)
- [The minimal height hypothesis](six-contact-min.md)
- [The slot conditions](../route-k/slot-conditions.md)
- [The certified rank hypothesis in infinitely-many-points form](../rank/infinitely-many-points/certified-rank-inf.md)
- [The Tian–Yuan–Zhang hypothesis in infinitely-many-points form](../rank/infinitely-many-points/certified-rank-tyz-inf.md)
- [The class-number hypothesis in infinitely-many-points form](../rank/infinitely-many-points/certified-rank-tyz-cl-inf.md)
- [The infinitely-many-points hypothesis on the two curves of a slot choice](../rank/infinitely-many-points/certified-rank-dl-inf.md)

## Proof depends on

- [The infinitely-many-points forms are equivalent to the positive-rank forms](../rank/infinitely-many-points/inf-iff-rk.md)
- [The main theorem from the positive-rank forms of the rank hypothesis](main-theorem-positive-rank.md)
- [The main theorem from positive rank on the two curves of a slot choice](main-theorem-two-curves.md)

## Sources

- [Theorem 1.1 and Lemma 1.2](../../sources/manuscript.md#theorem-11)
- [The infinitely-many-points forms](../../sources/rank-locators.md#the-infinitely-many-points-forms)
