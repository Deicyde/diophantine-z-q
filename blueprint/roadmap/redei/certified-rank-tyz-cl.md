---
article_id: af_0e8cc96c11f85b56d03c70e7
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.Rank5b.CertifiedRankTYZCl
---

# The certified rank hypothesis with class numbers

The hypothesis CR₃^TYZ_Cl is the following assertion. Let $d$ be squarefree with
$d\equiv5\pmod8$. If $|\mathrm{Sel}_2(C_d)|=8$ and the genus sum of class numbers
$T^{\rm Cl}_{5b}(d)$ is $1$, then for every $(a,b)\in\mathrm{Sel}_2(C_d)$ the 2-covering $D_{a,b}$
of $C_d$ has a rational point; that is, every 2-Selmer class of $C_d$ comes from a rational point.

CR₃^TYZ_Cl is not proved here; it is a hypothesis, stated in Tian, Yuan and Zhang's own terms,
with their genus class numbers $g(d_B)$, so that no Rédei formula enters its justification. It
rests on the following:

- *Tian–Yuan–Zhang*, Theorem 3.5 and the argument of the proof of their Theorem 3.5(2) (§3.3), as
  completed in nt-tyz §4 (Proposition N): for squarefree $d\equiv5\pmod8$, if the genus sum
  $\sum_{d_0\equiv7,\,d_1\equiv3\,(8)}g(d_0)g(d_1)\mathcal L_1(d/d_0d_1)$, which is
  $T^{\rm Cl}_{5b}(d)$ modulo $2$, is odd, then $L(C_d,s)$ vanishes to order exactly one at $s=1$.
  Here $\mathcal L_1(m)$ is the sum, over the set partitions of the primes of $m$ into blocks $B$
  with $d_B\equiv1\pmod8$, of $\prod_B g(d_B)$.
- *Gross–Zagier*, over an auxiliary imaginary quadratic field satisfying the Heegner hypothesis
  with $L(C_d^K,1)\ne0$: analytic rank one gives $\operatorname{rank}C_d(\mathbb Q)\ge1$.
- The step from positive rank to every Selmer class: when $|\mathrm{Sel}_2(C_d)|=8$ and $C_d$ has
  a rational point of infinite order, every 2-Selmer class of $C_d$ comes from a rational point.
  This step is proved
  ([positive rank and a Selmer group of order eight give every Selmer class](../rank/two-descent/every-selmer-class.md)),
  with [Mordell–Weil for the congruent number curves](../rank/mordell-weil/finite-generation.md).

By [Rédei's formula](redei-formula.md), CR₃^TYZ_Cl is equivalent to the hypothesis CR₃^TYZ stated
with Rédei's $g$ ([CR₃ with class numbers is CR₃^TYZ](class-number-hypothesis.md)).

## Depends on

- [The genus sum of class numbers](class-number-genus-sum.md)
- [The 2-Selmer group of a congruent number curve](../selmer/selmer-group.md)
- [The 2-coverings of a congruent number curve](../selmer/coverings.md)

## Sources

- [The hypothesis in class-number form](../../sources/redei-locators.md#the-hypothesis-in-class-number-form)
- [Tian-Yuan-Zhang](../../sources/redei-locators.md#tian-yuan-zhang)
- [Proposition N](../../sources/rank-5b-locators.md#proposition-n)
- [Gross-Zagier over an auxiliary field](../../sources/rank-5b-locators.md#gross-zagier-over-an-auxiliary-field)
