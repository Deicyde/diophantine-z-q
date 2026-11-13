---
article_id: af_63558bbd8fcce7c291b80c9c
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Contrib.GaussFE.frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagier, ZInQ.Contrib.GaussFE.certifiedRankTYZClRk_of_readingA_grossZagier
---

# The main theorem from the minimal height hypothesis, reading A and Gross–Zagier

Assume Tian–Yuan–Zhang's Theorem 3.5(2) in reading A and the Gross–Zagier statement. Then the
positive-rank class-number hypothesis CR₃^TYZ_Cl,Rk holds. If the minimal height hypothesis holds
as well, then the target statement holds: some integer polynomial in $292{,}890{,}231{,}905$
variables, of degree below $2\uparrow\uparrow7$ and with coefficients below $2\uparrow\uparrow8$,
has rational zero projection to its first variable exactly $\mathbb Z$.

Here $C_d$ is the curve $y^2=x^3-d^2x$ over $\mathbb Q$, for a natural number $d$, and $L(E,s)$ is
the L-series of a Weierstrass curve $E$ over $\mathbb Q$, as in [the main theorem](main-theorem.md).
An *entire continuation* of $L(E,s)$ is a function $F:\mathbb C\to\mathbb C$, complex
differentiable everywhere, with $F(s)=L(E,s)$ whenever $\operatorname{Re}s>3/2$
([entire continuations](../rank/literature/l-series-continuation.md)). The order of vanishing of an
entire function at a point is its order there as an analytic function, a value in
$\{0,1,2,\dots\}\cup\{\infty\}$. $T^{\rm Cl}_{5a}(d)$ and $T^{\rm Cl}_{5b}(d)$ in $\mathbb Z/2$ are
the [first genus sum](../rank/literature/genus-sum-5a.md) and the
[genus sum of class numbers](../redei/class-number-genus-sum.md) of row 5b. The hypotheses and the
intermediate conclusion are:

- Theorem 3.5(2) in reading A: for every squarefree natural number $d\equiv5\pmod8$ and every
  entire continuation $F$ of $L(C_d,s)$ whose order of vanishing at $s=1$ is at least $2$,
  $T^{\rm Cl}_{5a}(d)=0$ and $T^{\rm Cl}_{5b}(d)=0$ in $\mathbb Z/2$;
- the Gross–Zagier statement: for every Weierstrass curve $E$ over $\mathbb Q$ with nonzero
  discriminant and every entire continuation $F$ of $L(E,s)$ whose order of vanishing at $s=1$ is
  exactly $1$, $E(\mathbb Q)$ has a point of infinite order;
- the minimal height hypothesis: for every $u\in\mathbb Q\setminus\mathcal C$,
  $h(u)\le H_6(D)\,M_{S_{\rm mul}}(u)^{24}$, with the notation of
  [the minimal height hypothesis](six-contact-min.md);
- CR₃^TYZ_Cl,Rk, the conclusion of the first part: for every natural number $d$ with
  $d\equiv5\pmod8$, $d$ squarefree and $T^{\rm Cl}_{5b}(d)=1$, the curve $C_d$ has a rational point
  of infinite order.

These are three of the five hypotheses of [the main theorem](main-theorem.md); its other two, the
functional equation of $L(C_d,s)$ on the strip $0<\operatorname{Re}s<2$ and Hecke's continuation,
are proved ([the functional equation holds](../rank/literature/hecke/functional-equation-holds.md),
[Hecke's continuation holds](../rank/literature/hecke/hecke-continuation-holds.md)). None of the
three hypotheses of this theorem is proved here. The Gross–Zagier statement is a textbook theorem (Gross–Zagier 1986, with an
auxiliary imaginary quadratic field and modularity). Reading A is one reading of Tian–Yuan–Zhang's
genus sums. No refereed text found by the project's literature search, which AI agents carried
out, states it explicitly; Tian–Yuan–Zhang's introductory theorem with the same parity criteria,
read literally, is false; and their proof passes through their Proposition 3.4, whose proof is only
sketched in the arXiv version; the journal's proof was not assessed on this point. A new argument,
Proposition N, reviewed twice by AI models and never by a human, is supporting evidence, not a proof
of reading A. The minimal height
hypothesis is the one instance of the manuscript's six-contact height estimate that the proof uses;
the proof of that estimate combines refereed theorems and exact computations with new arguments,
the manuscript's and this project's, reviewed only by AI models, and it is not a published theorem.

**Proof sketch.** Gauss's count of the points of $y^2=x^3-x$ over $\mathbb F_p$, for primes
$p\equiv1\pmod4$, is proved
([Gauss's point count holds](../rank/literature/hecke/gauss/gauss-point-count-holds.md)).
Reading A, the Gross–Zagier statement and Gauss's point count imply CR₃^TYZ_Cl,Rk
([CR₃^TYZ_Cl,Rk from reading A, Gross–Zagier and Gauss's point count](../rank/literature/hecke/certified-rank-of-gauss-count.md)
(2)). This proves the first part. That proof uses Hecke's continuation only for squarefree
$d\equiv5\pmod8$: from Gauss's count it obtains, for those $d$, an entire continuation of
$L(C_d,s)$ and the functional equation on the strip; when $T^{\rm Cl}_{5b}(d)=1$, reading A
bounds the order of vanishing at $s=1$ by $1$, the functional equation gives vanishing at the
centre, and the Gross–Zagier statement then gives a point of infinite order.

For the second, [the main theorem from the positive-rank forms](main-theorem-positive-rank.md), in
its form with the minimal height hypothesis and CR₃^TYZ_Cl,Rk, gives the target. The proof does not
pass through the five-hypothesis main theorem.

## Depends on

- [The target statement](frozen-target.md)
- [The minimal height hypothesis](six-contact-min.md)
- [Entire continuations of the L-series of an elliptic curve](../rank/literature/l-series-continuation.md)
- [The first genus sum $T^{\rm Cl}_{5a}$](../rank/literature/genus-sum-5a.md)
- [The genus sum of class numbers](../redei/class-number-genus-sum.md)
- [Gross–Zagier: a simple zero gives a point of infinite order](../rank/literature/gross-zagier.md)
- [Tian–Yuan–Zhang's Theorem 3.5(2) in reading A](../rank/literature/tyz-reading-a.md)
- [The class-number hypothesis in positive-rank form](../rank/certified-rank-tyz-cl-rk.md)

## Proof depends on

- [Gauss's point count holds](../rank/literature/hecke/gauss/gauss-point-count-holds.md)
- [CR₃^TYZ_Cl,Rk from reading A, Gross–Zagier and Gauss's point count](../rank/literature/hecke/certified-rank-of-gauss-count.md)
- [The main theorem from the positive-rank forms of the rank hypothesis](main-theorem-positive-rank.md)

## Sources

- [Theorem 1.1 and Lemma 1.2](../../sources/manuscript.md#theorem-11)
- [The literature form of CR3](../../sources/rank-locators.md#the-literature-form-of-cr3)
- [Reading A of Tian-Yuan-Zhang](../../sources/rank-locators.md#reading-a-of-tian-yuan-zhang)
- [Tian-Yuan-Zhang](../../sources/rank-locators.md#tian-yuan-zhang)
- [Hecke and Deuring](../../sources/rank-locators.md#hecke-and-deuring)
- [The functional equation and the root number](../../sources/rank-locators.md#the-functional-equation-and-the-root-number)
- [Gross-Zagier](../../sources/rank-locators.md#gross-zagier)
- [The Hecke section](../../sources/hecke-locators.md#the-hecke-section)
- [The trust statement for H](../../sources/height-locators.md#the-trust-statement-for-h)
