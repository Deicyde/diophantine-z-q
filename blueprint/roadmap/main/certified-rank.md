---
article_id: af_f29543d708a24f1e27d766f9
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.CertifiedRank
---

# The certified rank hypothesis

For an integer $d$ let $C_d$ be the congruent number curve $y^2=x^3-d^2x$. The certified rank
hypothesis CR₃ is the following assertion. Let $d$ be a squarefree positive integer with
$d\equiv5\pmod8$, and let $a$ be a squarefree integer dividing $d$ with $|a|\equiv7\pmod8$.
Suppose that the Selmer system $\Sigma(\mathcal C_d)$ of the configuration of $d$ has exactly $8$
solutions and that one of them has first coordinate the class of $a$, that is
$a_0=[a<0]$, $a_1=0$ and $u_p=[p\mid a]$ for the primes $p\mid d$. Then $C_d$ has a rational
point $(x,y)$ with $x\ne0$ and $x/a$ a square in $\mathbb Q$.

CR₃ is a statement about Legendre symbols and rational points only; no Selmer group enters it.
It rests on the following theorems. Proposition 0 is proved
([Proposition 0](../selmer/proposition-0.md)), so CR₃ follows from its Selmer form
([CR₃ from its Selmer form](../selmer/certified-rank-of-sel.md)). So are the elementary steps of
route (i), namely the rule of row 5b ([Theorem 4.3](../rank-5b/theorem-4-3.md)) with
[Corollary 4.4](../rank-5b/corollary-4-4.md), the identity of the row-5b determinant with the genus
sum ([Theorem 3.6](../rank-5b/genus-sum/theorem-3-6.md)) and
[Rédei's formula](../redei/redei-formula.md), and so is the last step below, from positive rank to
every Selmer class ([RK9](../rank/two-descent/every-selmer-class.md), with
[Mordell–Weil for $C_d$](../rank/mordell-weil/finite-generation.md)). The analytic and rank
theorems are not proved here.

- *Proposition 0* (descent-alt §4.1; its place-2 rows for $d\equiv5\pmod8$ are rechecked in
  slot-k §2.1) identifies the solutions of $\Sigma(\mathcal C_d)$ with the 2-Selmer group
  $\mathrm{Sel}_2(C_d)$, so the hypotheses say that $\dim\mathrm{Sel}_2(C_d)=3$ and that $a$ is a
  first Kummer coordinate of $\mathrm{Sel}_2(C_d)$.
- *Positive rank*, by route (i). For $d\equiv5\pmod8$ with $|\mathrm{Sel}_2(C_d)|=8$ and a
  first coordinate with $|a|\equiv7\pmod8$, the shape CR₃ assumes, an elementary computation (the
  row-5b determinant of Smith's Monsky matrices, reproved in tyz-5b §§2–4) shows that the genus sum
  $T_{5b}(d)$ of Tian, Yuan and Zhang is odd. Their Theorem 3.5 and the argument of the proof of
  their Theorem 3.5(2), as completed in nt-tyz §4 by Proposition N, then give that $L(C_d,s)$
  vanishes to order exactly one at $s=1$. Gross–Zagier, applied over an auxiliary imaginary
  quadratic field $K$ that satisfies the Heegner hypothesis and has $L(C_d^K,1)\ne0$
  (Bump–Friedberg–Hoffstein), then gives $\operatorname{rank}C_d(\mathbb Q)\ge1$; $C_d$ is modular
  because it has complex multiplication by $\mathbb Z[i]$. Tian–Yuan–Zhang and Gross–Zagier are
  published. The form of TYZ used is the one their proof gives, which rests on their
  Proposition 3.4, whose proof is a sketch; Proposition N replaces that step by a direct parity
  count, and it is not refereed.
- *Route (ii)*, an alternative that is not needed: Kriz's 2-converse
  theorem (Theorems 10.13 and 10.17(2), an unrefereed preprint) with the corank lemma
  (the Cassels–Tate pairing on $Ш(C_d)/Ш(C_d)_{\rm div}$ is nondegenerate and alternating, so
  $\dim(Ш/Ш_{\rm div})[2]$ is even; no finiteness of $Ш$ is assumed) gives
  $\operatorname{rank}C_d(\mathbb Q)=1$ and $Ш(C_d)[2]=0$.
- Then $\dim C_d(\mathbb Q)/2C_d(\mathbb Q)=2+\operatorname{rank}C_d(\mathbb Q)$ is at least
  $3=\dim\mathrm{Sel}_2(C_d)$, so the Kummer map is onto
  $\mathrm{Sel}_2(C_d)$ ([RK9](../rank/two-descent/every-selmer-class.md)) and the class $a$ comes
  from a point $P$, which may be taken of infinite order (replace $P$ by $P+2Q$). The torsion
  classes are $1,-1,d,-d$, which $a$ is not since
  $|a|\equiv7$ and $d\equiv5\pmod8$. A point of infinite order has $x\notin\{0,\pm d\}$, so its first
  Kummer coordinate is the class of $x$: $x\in a\mathbb Q^{*2}$.

The congruences $d\equiv5$, $|a|\equiv7\pmod8$ are exactly what the descent lemma produces, so
CR₃ is as narrow as the proof allows short of naming the configurations of the slot
construction. A form that names them, with positive rank as its conclusion, is
[CR₃^DL,Rk](../rank/two-curves/certified-rank-dl-rk.md); it follows from the positive-rank forms
CR₃^Rk and CR₃^TYZ,Rk, and [the main theorem also holds](main-theorem-two-curves.md) under it and
[under the positive-rank forms](main-theorem-positive-rank.md) of the hypothesis
([the positive-rank chapter](../rank/README.md)). CR₃ is not proved here; it is a
hypothesis of the main theorem, and it implies pole completeness for the pole polynomial with the
curves $x+\ell$.

## Depends on

- [The configuration of an odd number and Selmer certificates](../route-k/prime-configuration.md)

## Sources

- [The Lean plan](../../sources/route-k-locators.md#the-lean-plan)
- [The deep input on published theorems](../../sources/route-k-locators.md#the-deep-input-on-published-theorems)
- [Proposition 0](../../sources/route-k-locators.md#proposition-0)
- [The trust statement for CR3](../../sources/route-k-locators.md#the-trust-statement-for-cr3)
- [Tian-Yuan-Zhang](../../sources/route-k-locators.md#tian-yuan-zhang)
- [Proposition N](../../sources/rank-5b-locators.md#proposition-n)
- [Gross-Zagier over an auxiliary field](../../sources/rank-5b-locators.md#gross-zagier-over-an-auxiliary-field)
- [Kriz](../../sources/route-k-locators.md#kriz)
- [Cassels-Tate](../../sources/route-k-locators.md#cassels-tate)
