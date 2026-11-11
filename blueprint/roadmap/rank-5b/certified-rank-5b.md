---
article_id: af_7f47b80a1f14d4ae4c83477b
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.Rank5b.CertifiedRank5b
---

# The certified rank hypothesis in row-5b form

The hypothesis CR₃^5b is the following assertion. Let $n>0$ be squarefree with
$n\equiv5\pmod8$. If $|\mathrm{Sel}_2(C_n)|=8$ and the determinant of Smith's row-5b matrix
$M_{5b}$, built from the Legendre symbols of the primes of $n$, is $1$, then for every
$(a,b)\in\mathrm{Sel}_2(C_n)$ the 2-covering $D_{a,b}$ of $C_n$ has a rational point; that is, every
2-Selmer class of $C_n$ comes from a rational point.

CR₃^5b is not proved here; it is a hypothesis, used only through CR₃^Sel, which it implies. It
follows from the hypothesis CR₃^TYZ in the terms of Tian, Yuan and Zhang ([CR₃^TYZ implies
CR₃^5b](certified-rank-5b-of-tyz.md)). It rests on the following. The first and the last are
theorems here, the middle two are not:

- *Row 5b of Smith's table* (elementary, reproved in tyz-5b §§2–3 by a forest expansion of
  determinants and Rédei's formulas for the 4-ranks of class groups; here
  [Theorem 3.6](genus-sum/theorem-3-6.md) and [Rédei's formula](../redei/redei-formula.md) through
  [the agreement of the two genus sums](../redei/genus-sums-agree.md)): for squarefree
  $n\equiv5\pmod8$,
  $\det M_{5b}$ equals the genus sum
  $T_{5b}(n)=\sum_{d_0\equiv7,\,d_1\equiv3\,(8)}g(d_0)g(d_1)\mathcal L_1(n/d_0d_1)$ modulo $2$, where
  $g(d)$ is the parity of $\#2\mathrm{Cl}(\mathbb Q(\sqrt{-d}))$ and $\mathcal L_1(m)$ is the sum,
  over the set partitions of the primes of $m$ into blocks $B$ with $d_B\equiv1\pmod8$ ($d_B$ the
  product of the primes in $B$), of $\prod_B g(d_B)$.
- *Tian–Yuan–Zhang*, Theorem 3.5 and the argument of the proof of their Theorem 3.5(2) (§3.3), as
  completed in nt-tyz §4 (Proposition N): if $T_{5b}(n)$ is odd, then their invariant
  $\mathcal L(n)$ is nonzero, so $L(C_n,s)$ vanishes to order exactly one at $s=1$ (the root
  number is $-1$ for $n\equiv5\pmod8$). The form used is the one their proof gives; it rests on
  their Proposition 3.4, whose proof is a sketch, and nt-tyz §4 proves it directly. Their statement
  groups this sum with another (tyz-5b §1.2).
- *Gross–Zagier*, over an auxiliary imaginary quadratic field $K$ that satisfies the Heegner
  hypothesis and has $L(C_n^K,1)\ne0$ (Bump–Friedberg–Hoffstein): then
  $\operatorname{rank}C_n(\mathbb Q)\ge1$.
- Then $\dim C_n(\mathbb Q)/2C_n(\mathbb Q)=2+\operatorname{rank}C_n(\mathbb Q)\ge3=\dim\mathrm{Sel}_2(C_n)$,
  so the Kummer map is onto
  $\mathrm{Sel}_2(C_n)$ and every Selmer class comes from a rational point
  ([RK9](../rank/two-descent/every-selmer-class.md), with [Mordell–Weil for
  $C_n$](../rank/mordell-weil/finite-generation.md)).

Compared with CR₃^Sel, only the 2-adic condition changes: "some Selmer class has
$|a|\equiv7\pmod8$" becomes "$\det M_{5b}=1$", which it implies. So CR₃^5b is logically stronger
than CR₃^Sel, but it is stated in the terms of Smith's table, one step closer to Tian, Yuan and
Zhang's own statement.

## Depends on

- [Smith's matrices $L$, $M_1$ and $M_{5b}$](smith-matrices.md)
- [The certified rank hypothesis in Selmer form](../selmer/certified-rank-sel.md)

## Sources

- [Row 5b of Smith's table](../../sources/rank-5b-locators.md#row-5b-of-smiths-table)
- [Tian-Yuan-Zhang](../../sources/rank-5b-locators.md#tian-yuan-zhang)
- [Proposition N](../../sources/rank-5b-locators.md#proposition-n)
- [Gross-Zagier over an auxiliary field](../../sources/rank-5b-locators.md#gross-zagier-over-an-auxiliary-field)
- [The trust statement for CR3](../../sources/route-k-locators.md#the-trust-statement-for-cr3)
- [Smith](../../sources/rank-5b-locators.md#smith)
