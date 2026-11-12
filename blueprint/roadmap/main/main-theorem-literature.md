---
article_id: af_c1f83ed4f7b6db36e1c2f853
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzRow5b_functionalEquation5_grossZagier, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_jHeightBound_certifiedRankTYZClRk, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_jHeightBound_tyzRow5b_functionalEquation5_grossZagier
---

# The main theorem from the $j$-form and the L-series statements

The target statement holds under each of the following three sets of hypotheses:

1. the minimal height hypothesis, Tian–Yuan–Zhang's row 5b, the functional equation of $L(C_d,s)$
   on the strip $0<\operatorname{Re}s<2$, and the Gross–Zagier statement;
2. the $j$-form of the height hypothesis at $S=S_{\rm mul}$ and CR₃^TYZ_Cl,Rk;
3. the $j$-form of the height hypothesis at $S=S_{\rm mul}$, Tian–Yuan–Zhang's row 5b, the
   functional equation of $L(C_d,s)$ on the strip $0<\operatorname{Re}s<2$, and the Gross–Zagier
   statement.

Here $C_d$ is the curve $y^2=x^3-d^2x$, and an
[entire continuation](../rank/literature/l-series-continuation.md) of the L-series $L(E,s)$ of a
Weierstrass curve $E$ over $\mathbb Q$ is a function $F:\mathbb C\to\mathbb C$, complex
differentiable everywhere, with $F(s)=L(E,s)$ for $\operatorname{Re}s>3/2$. The hypotheses are:

- Tian–Yuan–Zhang's row 5b: for every squarefree natural number $d\equiv5\pmod8$ whose genus sum of
  class numbers $T^{\rm Cl}_{5b}(d)$ is $1$ in $\mathbb Z/2$, $L(C_d,s)$ has an entire continuation
  whose order of vanishing at $s=1$ is at most $1$;
- the functional equation on the strip: for every squarefree natural number $d\equiv5\pmod8$, every
  entire continuation $F$ of $L(C_d,s)$ and every complex $s$ with $0<\operatorname{Re}s<2$,
  $\Lambda(2-s)=-\Lambda(s)$, where $\Lambda(s)=(32d^2)^{s/2}(2\pi)^{-s}\Gamma(s)F(s)$ (conductor
  $32d^2$, root number $-1$);
- the Gross–Zagier statement: for every elliptic curve $E$ over $\mathbb Q$ (a Weierstrass equation
  with nonzero discriminant) and every entire continuation $F$ of $L(E,s)$ with order of vanishing
  exactly $1$ at $s=1$, $E(\mathbb Q)$ has a point of infinite order;
- CR₃^TYZ_Cl,Rk: for every squarefree natural number $d\equiv5\pmod8$ with $T^{\rm Cl}_{5b}(d)=1$,
  $C_d(\mathbb Q)$ has a point of infinite order;
- the $j$-form at $S_{\rm mul}$: for every $u\in\mathbb Q\setminus\mathcal C$,
  $$h(J(u))\le(40\cdot10^4\cdot2^{24}+22)\,\max\bigl(1,C_{\rm cm},Q_D^{17}\bigr)\,M_{S_{\rm mul}}(u)^{24},$$
  where $J$ is [the Hauptmodul value](j-form/hauptmodul-value.md), and $\mathcal C$, $h$,
  $C_{\rm cm}$, $Q_D$, $S_{\rm mul}$ and $M_S(u)$ are as in
  [the minimal height hypothesis](six-contact-min.md) and
  [the $j$-form of the height hypothesis](j-form/j-height-bound.md).

The functional equation (Hecke and Deuring, with root number $-1$ for $d\equiv5\pmod8$ by
Birch–Stephens) and Gross–Zagier (with an auxiliary imaginary quadratic field and modularity)
follow from textbook theorems. Row 5b is Tian–Yuan–Zhang's Theorem 3.5(2) for $d\equiv5\pmod8$ in
reading A, in contrapositive form and for the row $(7,3)$ only, with Hecke's continuation for the
existence of the continuation
([row 5b from reading A and Hecke's continuation](../rank/literature/tyz-row-5b-of-reading-a.md)).
The only printed statement of reading A found so far is in an unrefereed preprint (the journal
version of their paper and Tian's expository accounts were not read); a proof written for this
project (Proposition N), with two automated reviews and no human review, derives it from their
unambiguous statements. The $j$-form is the bound that the project's trust statement for the
manuscript's proof of the six-contact estimate gives before its last step. That statement follows
the manuscript's argument, replaces some of its steps with arguments written for this project and
one with an argument from another version of the manuscript, and combines three of its bounds into
one that the manuscript does not display; many of its steps, including all of the manuscript's
new arguments, have had only automated reviews. It is not a published theorem. None of these
hypotheses is proved here.

**Proof sketch.** Taking $s=1$ in the functional equation gives
[vanishing at the centre](../rank/literature/root-number-vanishing-of-functional-equation.md):
every entire continuation of $L(C_d,s)$ vanishes at $1$. For squarefree $d\equiv5\pmod8$ with
$T^{\rm Cl}_{5b}(d)=1$, row 5b gives an entire continuation of order at most $1$ at $s=1$, and
since it vanishes there its order is [exactly $1$](../rank/literature/analytic-rank-one.md). As
$d\ne0$, $C_d$ is an elliptic curve, so the Gross–Zagier statement gives a point of infinite
order: this is [CR₃^TYZ_Cl,Rk](../rank/literature/certified-rank-tyz-cl-rk-of-literature.md). The
[$j$-form at $S_{\rm mul}$ implies the minimal height hypothesis](j-form/six-contact-min-of-j-height-bound.md),
through $12h(u)\le h(J(u))+450$ for $u\notin\mathcal C$; since
$\max(1,C_{\rm cm},Q_D^{17})\,M_{S_{\rm mul}}(u)^{24}\ge1$, the constant $450$ is absorbed, and
$(40\cdot10^4\cdot2^{24}+22+450)/12\le2\cdot10^{13}$ gives the bound
$H_6(D)\,M_{S_{\rm mul}}(u)^{24}$. In each of the three cases this yields the
minimal height hypothesis and CR₃^TYZ_Cl,Rk, and the third form of
[the main theorem from the positive-rank forms](main-theorem-positive-rank.md) applies.

## Depends on

- [The target statement](frozen-target.md)
- [The minimal height hypothesis](six-contact-min.md)
- [The $j$-form of the height hypothesis](j-form/j-height-bound.md)
- [The Hauptmodul value $J(u)$](j-form/hauptmodul-value.md)
- [Entire continuations of the L-series of an elliptic curve](../rank/literature/l-series-continuation.md)
- [The class-number hypothesis in positive-rank form](../rank/certified-rank-tyz-cl-rk.md)
- [Tian–Yuan–Zhang's row 5b](../rank/literature/tyz-row-5b.md)
- [The functional equation of $L(C_d,s)$ on the strip $0<\operatorname{Re}s<2$](../rank/literature/functional-equation.md)
- [Gross–Zagier: a simple zero gives a point of infinite order](../rank/literature/gross-zagier.md)

## Proof depends on

- [The main theorem from the positive-rank forms of the rank hypothesis](main-theorem-positive-rank.md)
- [The functional equation gives vanishing at the centre](../rank/literature/root-number-vanishing-of-functional-equation.md)
- [Analytic rank one for the curves of row 5b](../rank/literature/analytic-rank-one.md)
- [Row 5b, vanishing at the centre and Gross–Zagier give CR₃^TYZ_Cl,Rk](../rank/literature/certified-rank-tyz-cl-rk-of-literature.md)
- [The $j$-form implies the minimal height hypothesis](j-form/six-contact-min-of-j-height-bound.md)

## Sources

- [Theorem 1.1 and Lemma 1.2](../../sources/manuscript.md#theorem-11)
- [The literature form of CR3](../../sources/rank-locators.md#the-literature-form-of-cr3)
- [The j-form of H](../../sources/height-locators.md#the-j-form-of-h)
- [Hecke and Deuring](../../sources/rank-locators.md#hecke-and-deuring)
- [The functional equation and the root number](../../sources/rank-locators.md#the-functional-equation-and-the-root-number)
- [Gross-Zagier](../../sources/rank-locators.md#gross-zagier)
- [Reading A of Tian-Yuan-Zhang](../../sources/rank-locators.md#reading-a-of-tian-yuan-zhang)
- [Proposition N](../../sources/rank-5b-locators.md#proposition-n)
- [Step F4](../../sources/height-locators.md#step-f4)
- [The trust statement for H](../../sources/height-locators.md#the-trust-statement-for-h)
