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
It rests on the following theorems. Proposition 0 is now formalized
([Proposition 0](../selmer/proposition-0.md)), so CR₃ follows from its Selmer form
([CR₃ from its Selmer form](../selmer/certified-rank-of-sel.md)), and so is the row-5b determinant
of route (i) ([Theorem 4.3](../rank-5b/theorem-4-3.md)); the rank-one theorems are not.

- *Proposition 0* (descent-alt §4.1; its place-2 rows for $d\equiv5\pmod8$ are rechecked in
  slot-k §2.1) identifies the solutions of $\Sigma(\mathcal C_d)$ with the 2-Selmer group
  $\mathrm{Sel}_2(C_d)$, so the hypotheses say that $\dim\mathrm{Sel}_2(C_d)=3$ and that $a$ is a
  first Kummer coordinate of $\mathrm{Sel}_2(C_d)$.
- *Rank one*, by either of two routes. (i) For $d\equiv5\pmod8$ and a first coordinate with
  $|a|\equiv3\pmod4$, an elementary computation (the row-5b determinant of Smith's Monsky
  matrices, reproved in tyz-5b §§2–4) shows that the genus sum $T_{5b}(d)$ of Tian, Yuan and Zhang
  is odd; the proof of their Theorem 3.5(2) then gives that $L(C_d,s)$ vanishes to order exactly
  one at $s=1$, and Gross–Zagier–Kolyvagin give $\operatorname{rank}C_d(\mathbb Q)=1$. Both are
  published; the form of TYZ used is the one their proof establishes. (ii) Kriz's 2-converse
  theorem (Theorems 10.13 and 10.17(2), an unrefereed preprint) with the corank lemma
  (Poonen–Stoll) gives $\operatorname{rank}C_d(\mathbb Q)=1$ and $Ш(C_d)[2]=0$.
- Then $\dim C_d(\mathbb Q)/2C_d(\mathbb Q)=2+1=\dim\mathrm{Sel}_2(C_d)$, so the Kummer map is onto
  $\mathrm{Sel}_2(C_d)$ and the class $a$ comes from a point $P$, which may be taken of infinite
  order (replace $P$ by $P+2Q$). The torsion classes are $1,-1,d,-d$, which $a$ is not since
  $|a|\equiv7$ and $d\equiv5\pmod8$. A point of infinite order has $x\notin\{0,\pm d\}$, so its first
  Kummer coordinate is the class of $x$: $x\in a\mathbb Q^{*2}$.

The congruences $d\equiv5$, $|a|\equiv7\pmod8$ are exactly what the descent lemma produces, so
CR₃ is as narrow as the proof allows short of naming the configurations of the slot
construction. It is not proved here; it is a hypothesis of the main theorem, and it implies
pole completeness for the pole polynomial with the curves $x+\ell$.

## Depends on

- [The configuration of an odd number and Selmer certificates](../route-k/prime-configuration.md)

## Sources

- [The Lean plan](../../sources/route-k-locators.md#the-lean-plan)
- [The deep input on published theorems](../../sources/route-k-locators.md#the-deep-input-on-published-theorems)
- [Proposition 0](../../sources/route-k-locators.md#proposition-0)
- [Tian-Yuan-Zhang](../../sources/route-k-locators.md#tian-yuan-zhang)
- [Gross-Zagier-Kolyvagin](../../sources/route-k-locators.md#gross-zagier-kolyvagin)
- [Kriz](../../sources/route-k-locators.md#kriz)
- [Poonen-Stoll](../../sources/route-k-locators.md#poonen-stoll)
