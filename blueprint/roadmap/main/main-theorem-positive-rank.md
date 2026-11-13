---
article_id: af_7cbf516087c0f7cc27ab10aa
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankRk, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZRk, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk
---

# The main theorem from the positive-rank forms of the rank hypothesis

Assume the minimal height hypothesis and the positive-rank form CR₃^Rk of the certified rank
hypothesis. Then the target statement holds. The theorem also holds under the minimal height hypothesis and
CR₃^TYZ,Rk, and under the minimal height hypothesis and CR₃^TYZ_Cl,Rk.

Here $C_d$ is the curve $y^2=x^3-d^2x$. Each of these hypotheses concludes only that $C_d(\mathbb Q)$
has a point of infinite order, which is what the published theorems give:

- CR₃^Rk: for squarefree positive $d\equiv5\pmod8$, if $|\mathrm{Sel}_2(C_d)|=8$ and some
  $(a,b)\in\mathrm{Sel}_2(C_d)$ has $|a|\equiv7\pmod8$, then $C_d(\mathbb Q)$ has a point of infinite
  order;
- CR₃^TYZ,Rk: for squarefree positive $d\equiv5\pmod8$ with odd genus sum $T_{5b}(d)$ of row 5b,
  $C_d(\mathbb Q)$ has a point of infinite order;
- CR₃^TYZ_Cl,Rk: the same with the genus sum of class numbers $T^{\mathrm{Cl}}_{5b}(d)$ odd.

No condition on the Selmer group enters the last two. Since
[CR₃^TYZ_Cl,Rk implies CR₃^TYZ,Rk](../rank/certified-rank-tyz-rk-of-cl-rk.md) and
[CR₃^TYZ,Rk implies CR₃^Rk](../rank/certified-rank-rk-of-tyz-rk.md), the form with CR₃^Rk assumes
the least of the three.

**Proof sketch.** Mordell–Weil for the congruent number curves holds, so each positive-rank form
gives the matching form whose conclusion is that every 2-Selmer class of $C_d$ comes from a rational
point: a point of infinite order and a Selmer group of order $8$ give every Selmer class (RK9). Thus
CR₃^Rk gives CR₃^Sel, and
[the main theorem from the Selmer form of the rank hypothesis](main-theorem-selmer.md) applies in its
form with the minimal height hypothesis and CR₃^Sel alone. Likewise CR₃^TYZ,Rk gives CR₃^TYZ and
CR₃^TYZ_Cl,Rk gives CR₃^TYZ_Cl, and
[the main theorem from the Tian–Yuan–Zhang forms](main-theorem-tyz.md) applies in its two forms.

## Depends on

- [The target statement](frozen-target.md)
- [The minimal height hypothesis](six-contact-min.md)
- [The certified rank hypothesis in positive-rank form](../rank/certified-rank-rk.md)
- [The Tian–Yuan–Zhang hypothesis in positive-rank form](../rank/certified-rank-tyz-rk.md)
- [The class-number hypothesis in positive-rank form](../rank/certified-rank-tyz-cl-rk.md)

## Proof depends on

- [CR₃^Sel from CR₃^Rk](../rank/certified-rank-sel-of-rk.md)
- [CR₃^TYZ from CR₃^TYZ,Rk](../rank/certified-rank-tyz-of-rk.md)
- [CR₃^TYZ_Cl from CR₃^TYZ_Cl,Rk](../rank/certified-rank-tyz-cl-of-rk.md)
- [The main theorem from the Selmer form of the rank hypothesis](main-theorem-selmer.md)
- [The main theorem from the Tian–Yuan–Zhang forms of the rank hypothesis](main-theorem-tyz.md)

## Sources

- [Theorem 1.1 and Lemma 1.2](../../sources/manuscript.md#theorem-11)
- [The positive-rank form](../../sources/rank-locators.md#the-positive-rank-form)
- [RK9](../../sources/rank-locators.md#rk9)
- [Mordell–Weil for the congruent number curves](../../sources/rank-locators.md#mordell-weil-for-the-congruent-number-curves)
