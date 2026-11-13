---
article_id: af_85e6d577c7de0fa238d647e3
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzThm35ReadingA_heckeContinuation_functionalEquation5_grossZagier
---

# The main theorem

Assume the minimal height hypothesis and four statements about L-series of elliptic curves: the
Gross–Zagier statement, the functional equation of $L(C_d,s)$ on the strip
$0<\operatorname{Re}s<2$, Hecke's continuation of $L(C_d,s)$, and Tian–Yuan–Zhang's Theorem 3.5(2)
in reading A. Then the target statement holds: some integer polynomial in
$292{,}890{,}231{,}905$ variables, of degree below $2\uparrow\uparrow7$ and with coefficients below
$2\uparrow\uparrow8$, has rational zero projection to its first variable exactly $\mathbb Z$.

Here $C_d$ is the curve $y^2=x^3-d^2x$ over $\mathbb Q$, for a natural number $d$. For a
Weierstrass curve $E$ over $\mathbb Q$, $L(E,s)$ is its L-series, the Dirichlet series whose
coefficients are those of the Euler product $\prod_p f_p(p^{-s})^{-1}$, where $f_p$ is the
local polynomial of a minimal model of $E$ over $\mathbb Q_p$; its value at $s$ is the sum of the
series where it converges absolutely, and $0$ elsewhere. An *entire continuation* of $L(E,s)$
is a function $F:\mathbb C\to\mathbb C$, complex differentiable everywhere, with $F(s)=L(E,s)$
whenever $\operatorname{Re}s>3/2$; two entire continuations of the same $L(E,s)$ are equal
([entire continuations](../rank/literature/l-series-continuation.md)). The order of vanishing of
an entire function at a point is its order there as an analytic function, a value in
$\{0,1,2,\dots\}\cup\{\infty\}$. $T^{\rm Cl}_{5a}(d)$ and $T^{\rm Cl}_{5b}(d)$ in $\mathbb Z/2$ are
the [first genus sum](../rank/literature/genus-sum-5a.md) and the
[genus sum of class numbers](../redei/class-number-genus-sum.md) of row 5b. The five hypotheses
are:

- the minimal height hypothesis: for every $u\in\mathbb Q\setminus\mathcal C$,
  $h(u)\le H_6(D)\,M_{S_{\rm mul}}(u)^{24}$, with the notation of
  [the minimal height hypothesis](six-contact-min.md);
- the Gross–Zagier statement: for every Weierstrass curve $E$ over $\mathbb Q$ with nonzero
  discriminant and every entire continuation $F$ of $L(E,s)$ whose order of vanishing at $s=1$ is
  exactly $1$, $E(\mathbb Q)$ has a point of infinite order;
- the functional equation on the strip: for every squarefree natural number $d\equiv5\pmod8$, every
  entire continuation $F$ of $L(C_d,s)$ and every complex $s$ with $0<\operatorname{Re}s<2$,
  $$\Lambda(2-s)=-\Lambda(s),\qquad \Lambda(s)=(32d^2)^{s/2}(2\pi)^{-s}\,\Gamma(s)\,F(s),$$
  where $(32d^2)^{s/2}=e^{(s/2)\log(32d^2)}$ and $(2\pi)^{-s}=e^{-s\log2\pi}$ (conductor $32d^2$,
  root number $-1$);
- Hecke's continuation: for every natural number $d\ne0$, $L(C_d,s)$ has an entire continuation;
- Theorem 3.5(2) in reading A: for every squarefree natural number $d\equiv5\pmod8$ and every
  entire continuation $F$ of $L(C_d,s)$ whose order of vanishing at $s=1$ is at least $2$,
  $T^{\rm Cl}_{5a}(d)=0$ and $T^{\rm Cl}_{5b}(d)=0$ in $\mathbb Z/2$.

Two of the five are proved: Hecke's continuation
([Hecke's continuation holds](../rank/literature/hecke/hecke-continuation-holds.md)) and the
functional equation on the strip
([the functional equation holds](../rank/literature/hecke/functional-equation-holds.md)), both
proved outright: they follow from Gauss's count of the points of $y^2=x^3-x$ over $\mathbb F_p$ for
primes $p\equiv1\pmod4$, which is itself proved here. The target therefore follows from the
other three, the minimal height hypothesis, the Gross–Zagier statement and Theorem 3.5(2) in
reading A
([the main theorem from the minimal height hypothesis, reading A and Gross–Zagier](main-theorem-reading-a-gross-zagier.md)),
and none of these three is proved here. The Gross–Zagier statement is a textbook theorem: Gross–Zagier
(1986) with an auxiliary imaginary quadratic field (Bump–Friedberg–Hoffstein 1990, or
Friedberg–Hoffstein 1995) and modularity (Breuil–Conrad–Diamond–Taylor 2001); Kolyvagin's conclusion
that the rank is exactly one is not used. The functional equation and Hecke's continuation are also textbook theorems: $C_d$ has complex
multiplication by $\mathbb Z[i]$, so $L(C_d,s)$ is the L-function of a Hecke character of
$\mathbb Q(i)$ (Hecke, Deuring), which is entire, with conductor $32d^2$ for odd squarefree $d$ and
root number $-1$ for squarefree $d\equiv5\pmod8$ (Birch–Stephens). The functional equation is
stated only on the strip, where $\Gamma(s)$ and $\Gamma(2-s)$ are both finite, and it is used only
at $s=1$. The proofs here do not rely on these sources; no original source of Hecke's continuation
was read, and the original source of the conductor and the functional equation has not been
read in full. The minimal height hypothesis is the one instance of the manuscript's six-contact
height estimate (its Theorem 4.1) that the proof uses; the proof of that estimate combines refereed
theorems and exact computations with new arguments, the manuscript's and this project's, reviewed
only by AI models, and it is not a published theorem.

**Tian–Yuan–Zhang.** The last hypothesis is a consequence of Theorem 3.5(2) of Tian, Yuan and Zhang
(arXiv:1411.4728v1; Asian J. Math. 21 (2017)) for $n=d\equiv5\pmod8$, under one reading of their
genus sums, reading A: the decompositions of $n$ are the set partitions of its primes, each counted
once, with a trivial factor allowed ([reading A](../rank/literature/tyz-reading-a.md)). It is needed
only when their invariant $\mathcal L(n)$ is $0$: they define $\mathcal L(n)$ from $L(C_n,1)$ or
$L'(C_n,1)$ and set it to $0$ exactly when the order of vanishing at $s=1$ is at least $2$. Their
printed hypothesis is a condition on their genus point $P(n)$, followed by an "i.e." that restates
it as the evenness of $2^{-\rho(n)}\mathcal L(n)$ and is not proved in the paper; when
$\mathcal L(n)=0$ the condition on $P(n)$ follows from the first assertion of their Theorem 3.5 and
their Lemma 3.18, so the "i.e." is not needed. No refereed text found by the project's literature search, which AI agents
carried out, states reading A explicitly; the one statement found is in an unrefereed preprint
(Smith). Their introductory theorem with the same parity criteria (Theorem 1.2 of the arXiv version,
Theorem 1.4 of the journal version) requires every factor to exceed $1$, and read that way it is
false in both versions: $d=26565$ and $d=33117$ are counterexamples (exact class-group computations
and explicit points giving rank at least $3$, not checked here). Their proof of Theorem 3.5(2)
passes through their Proposition 3.4, whose proof is only a sketch in the arXiv version; the
journal's proof was not assessed on this point, and the comparison of the two versions was made by
AI agents and not checked by a human. A new argument written for this project (Proposition N),
reviewed twice by AI models and never by a human, derives reading A from unambiguous results of the
arXiv version without that proposition. Its derivation of reading A from a restatement of those
results is proved here, but no proof checks that the restatement matches the paper, and only AI models have compared it with the paper; it is
supporting evidence, not a hypothesis of this theorem.

The target also holds under other hypotheses. Hecke's continuation and reading A imply
Tian–Yuan–Zhang's row 5b (proof below), so the form of
[the main theorem from the $j$-form and the L-series statements](main-theorem-literature.md) with
the minimal height hypothesis, row 5b, the functional equation and the Gross–Zagier statement
assumes less. The four L-series statements imply the certified rank hypothesis CR₃, so
[the main theorem from two hypotheses](main-theorem-two-hypotheses.md), under the minimal height
hypothesis and CR₃, assumes less again; CR₃ is not a statement of the literature.
[The main theorem from three hypotheses](main-theorem-three-hypotheses.md) assumes the minimal
height hypothesis, CR₃ and the manuscript's twenty-two-prime pattern.

**Proof sketch.** Let $d\equiv5\pmod8$ be squarefree with $T^{\rm Cl}_{5b}(d)=1$. Then $d\ne0$,
so Hecke's continuation gives an entire continuation $F$ of $L(C_d,s)$. If its order of vanishing
at $s=1$ were at least $2$, reading A would give $T^{\rm Cl}_{5b}(d)=0$; so the order is at most
$1$. This is Tian–Yuan–Zhang's row 5b
([row 5b from reading A and Hecke's continuation](../rank/literature/tyz-row-5b-of-reading-a.md)),
and [the main theorem from the $j$-form and the L-series statements](main-theorem-literature.md),
in its form with the minimal height hypothesis, row 5b, the functional equation and the
Gross–Zagier statement, gives the target.

That form is proved as follows. Taking $s=1$, which lies in the strip, the functional equation
gives $\Lambda(1)=-\Lambda(1)$, so $\Lambda(1)=0$; since $\Gamma(1)=1$ and the two powers are
nonzero, every entire continuation of $L(C_d,s)$ vanishes at $s=1$
([vanishing at the centre](../rank/literature/root-number-vanishing-of-functional-equation.md)).
With row 5b the order of vanishing is exactly $1$
([analytic rank one](../rank/literature/analytic-rank-one.md)). The discriminant of $C_d$ is
$64d^6\ne0$, so the Gross–Zagier statement gives a point of infinite order on $C_d$. This is the
positive-rank class-number hypothesis CR₃^TYZ_Cl,Rk
([its derivation](../rank/literature/certified-rank-tyz-cl-rk-of-literature.md)), and the form of
[the main theorem from the positive-rank forms](main-theorem-positive-rank.md) with the minimal
height hypothesis and CR₃^TYZ_Cl,Rk applies. Its proof passes to CR₃: when
$|\mathrm{Sel}_2(C_d)|=8$, a point of infinite order puts a rational point in every 2-Selmer class
(RK9, with Mordell–Weil for $C_d$), so CR₃^TYZ_Cl,Rk gives
[CR₃^TYZ_Cl](../rank/certified-rank-tyz-cl-of-rk.md); Rédei's formula turns it into
[CR₃^TYZ](../redei/class-number-hypothesis.md); Theorem 3.6 gives
[CR₃^5b](../rank-5b/certified-rank-5b-of-tyz.md); Corollary 4.4 gives
[CR₃^Sel](../rank-5b/certified-rank-sel-of-5b.md); Proposition 0 gives
[CR₃](../selmer/certified-rank-of-sel.md). Finally
[the main theorem from two hypotheses](main-theorem-two-hypotheses.md) applies to the minimal
height hypothesis and CR₃: route AP gives the completeness of the multiplication template, and CR₃
gives pole completeness.

## Depends on

- [The target statement](frozen-target.md)
- [The minimal height hypothesis](six-contact-min.md)
- [Entire continuations of the L-series of an elliptic curve](../rank/literature/l-series-continuation.md)
- [The first genus sum $T^{\rm Cl}_{5a}$](../rank/literature/genus-sum-5a.md)
- [The genus sum of class numbers](../redei/class-number-genus-sum.md)
- [Gross–Zagier: a simple zero gives a point of infinite order](../rank/literature/gross-zagier.md)
- [The functional equation of $L(C_d,s)$ on the strip $0<\operatorname{Re}s<2$](../rank/literature/functional-equation.md)
- [Hecke's continuation of $L(C_d,s)$](../rank/literature/hecke-continuation.md)
- [Tian–Yuan–Zhang's Theorem 3.5(2) in reading A](../rank/literature/tyz-reading-a.md)

## Proof depends on

- [Row 5b from reading A and Hecke's continuation](../rank/literature/tyz-row-5b-of-reading-a.md)
- [The main theorem from the $j$-form and the L-series statements](main-theorem-literature.md)

## Sources

- [Theorem 1.1 and Lemma 1.2](../../sources/manuscript.md#theorem-11)
- [The literature form of CR3](../../sources/rank-locators.md#the-literature-form-of-cr3)
- [Reading A of Tian-Yuan-Zhang](../../sources/rank-locators.md#reading-a-of-tian-yuan-zhang)
- [Tian-Yuan-Zhang](../../sources/rank-locators.md#tian-yuan-zhang)
- [Proposition N](../../sources/rank-5b-locators.md#proposition-n)
- [Hecke and Deuring](../../sources/rank-locators.md#hecke-and-deuring)
- [The functional equation and the root number](../../sources/rank-locators.md#the-functional-equation-and-the-root-number)
- [Gross-Zagier](../../sources/rank-locators.md#gross-zagier)
- [The trust statement for H](../../sources/height-locators.md#the-trust-statement-for-h)
