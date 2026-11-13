---
article_id: af_110e5f3790aa6b1889d190ba
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.Rank5b.CertifiedRankTYZ
---

# The certified rank hypothesis in Tian–Yuan–Zhang form

The hypothesis CR₃^TYZ is the following assertion. Let $n$ be squarefree with $n\equiv5\pmod8$. If
$|\mathrm{Sel}_2(C_n)|=8$ and the genus sum $T_{5b}(n)$ is $1$, then for every
$(a,b)\in\mathrm{Sel}_2(C_n)$ the 2-covering $D_{a,b}$ of $C_n$ has a rational point; that is, every
2-Selmer class of $C_n$ comes from a rational point.

CR₃^TYZ is not proved here; it is a hypothesis. It rests on the following. The second and the last
are theorems here, the other two are not:

- *Tian–Yuan–Zhang*, Theorem 3.5 (first assertion) and the argument of the proof of their Theorem
  3.5(2) (§3.3), as completed in nt-tyz §4 (Proposition N): for squarefree $n\equiv5\pmod8$, if
  $\sum_{d_0\equiv7,\,d_1\equiv3\,(8)}g(d_0)g(d_1)\mathcal L_1(n/d_0d_1)$ is odd, then $L(C_n,s)$
  vanishes to order exactly one at $s=1$ (the root number is $-1$). Here $g(d)$ is the parity of
  $\#2\mathrm{Cl}(\mathbb Q(\sqrt{-d}))$ and $\mathcal L_1(m)$ is the sum of $\prod g$ over the
  partitions of the primes of $m$ into blocks $\equiv1\pmod8$. Their Theorem 1.2 is not cited in its
  literal form.
- *Rédei's formula*: for odd squarefree $n$ and every nonempty set $B$ of primes of $n$ with
  $d_B\equiv7,3$ or $1\pmod8$, $g_n(B)$ is the parity of $\#2\mathrm{Cl}(\mathbb Q(\sqrt{-d_B}))$. So
  $T_{5b}(n)$ is the genus sum of the previous item. This is a theorem here: [Rédei's
  formula](../redei/redei-formula.md).
- *Gross–Zagier*, over an auxiliary imaginary quadratic field $K$ that satisfies the Heegner
  hypothesis and has $L(C_n^K,1)\ne0$ (Bump–Friedberg–Hoffstein), for the curve
  $C_n$, which is modular because it has complex multiplication by $\mathbb Z[i]$: analytic rank one
  gives $\operatorname{rank}C_n(\mathbb Q)\ge1$.
- Then, as $C_n(\mathbb Q)[2]$ has order $4$, $\dim C_n(\mathbb Q)/2C_n(\mathbb Q)\ge3=\dim\mathrm{Sel}_2(C_n)$,
  so the Kummer map is onto $\mathrm{Sel}_2(C_n)$ and every Selmer class comes from a rational point.
  This is a theorem here: [Positive rank and a Selmer group of order eight give every Selmer class
  (RK9)](../rank/two-descent/every-selmer-class.md), with [Mordell–Weil for the congruent number
  curves](../rank/mordell-weil/finite-generation.md).

CR₃^TYZ differs from the row-5b form only in its last condition: $\det M_{5b}=1$ becomes
$T_{5b}(n)=1$. By [Theorem 3.6](genus-sum/theorem-3-6.md) the two conditions coincide for these $n$,
so CR₃^TYZ implies [CR₃^5b](certified-rank-5b.md) ([CR₃^TYZ implies
CR₃^5b](certified-rank-5b-of-tyz.md)). The form of the hypothesis with the class numbers
$\#2\mathrm{Cl}(\mathbb Q(\sqrt{-d_B}))$ in place of $g_n(B)$ is in the [Rédei chapter](../redei/README.md).

## Depends on

- [The genus sum $T_{5b}$](genus-sum/genus-sum.md)
- [The 2-Selmer group of a congruent number curve](../selmer/selmer-group.md)

## Sources

- [The hypothesis in Tian-Yuan-Zhang form](../../sources/rank-5b-locators.md#the-hypothesis-in-tian-yuan-zhang-form)
- [Proposition N](../../sources/rank-5b-locators.md#proposition-n)
- [Tian-Yuan-Zhang](../../sources/rank-5b-locators.md#tian-yuan-zhang)
- [Gross-Zagier over an auxiliary field](../../sources/rank-5b-locators.md#gross-zagier-over-an-auxiliary-field)
- [The trust statement for CR3](../../sources/route-k-locators.md#the-trust-statement-for-cr3)
