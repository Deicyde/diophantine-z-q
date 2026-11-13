# Locators for the positive-rank chapter

The positive-rank step is not in the manuscript. It is record RK9 of the project-authored audit
note `docs/research/pc-audit.md`; the positive-rank forms of the hypothesis follow the narrowing N2
of the project-authored note `docs/research/cr3-map-literature.md`; and the form on the two curves
of a slot choice is reviewed in the project-authored note `docs/research/rv-cr3-dl.md`, with the plan
`KERNEL_PLAN.md`. The section deriving CR₃^TYZ_Cl,Rk from three literature statements follows the
project-authored notes `docs/research/wk-cr3.md` (the plan and the statements) and
`docs/research/rv-lit.md` (its model review, whose verdict is to adopt with two changes), with the
paragraph of `KERNEL_PLAN.md` that records the result. These are notes written for this project,
not published sources. The standard
facts on the 2-descent and on heights, and the deep theorems behind the hypotheses, are cited at
the end.

## The complete 2-descent map

The map $P\mapsto(x-e_1,x-e_2)$ modulo squares on a curve $y^2=(x-e_1)(x-e_2)(x-e_3)$ with full
rational 2-torsion, with the stated values at the 2-torsion points, is a homomorphism with kernel
$2E(K)$: J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Springer (2009), Proposition
X.1.4, as cited by `docs/research/pc-audit.md` RK8, which records its use for $C_d$. The proposition
number was not rechecked against the book.

## Halving

`docs/research/cr3-map-literature.md` §8, N2, Lean cost (i): the Kummer map
$C_d(\mathbb Q)\to(\mathbb Q^*/\mathbb Q^{*2})^2$ is a homomorphism with kernel $2C_d(\mathbb Q)$, by
the lemma that $x$, $x\pm d$ squares make $(x,y)$ halvable (classical, elementary). The explicit half,
with $x'=x+r_1r_2+r_1r_3+r_2r_3$ where $r_i^2=x-e_i$, is the standard formula for curves with full
2-torsion.

## RK9

`docs/research/pc-audit.md` §3, record RK9 (and §2.2): if $\dim\mathrm{Sel}_2(C_d)=3$ and
$\operatorname{rank}C_d(\mathbb Q)\ge1$, then $C_d(\mathbb Q)/2C_d(\mathbb Q)$, which injects into
$\mathrm{Sel}_2$ and has dimension $2+\operatorname{rank}\ge3$, equals $\mathrm{Sel}_2$, so every
Selmer class comes from a rational point, which can be taken of infinite order. No pairing and no
finiteness of $Ш$ are needed. The count uses that $C_d(\mathbb Q)$ is finitely generated.

## Two-torsion of the congruent number curves

`docs/research/tyz-5b.md` §1.3, item "No prescribed class": $C_n(\mathbb Q)[2]=(\mathbb Z/2)^2$
(standard), so $\dim C_n(\mathbb Q)/2C_n(\mathbb Q)=2+\mathrm{rank}$.

## Mordell-Weil for the congruent number curves

`KERNEL_PLAN.md`, section "What can and cannot be formalized", the paragraph beginning "These
hypotheses all conclude": $C_d(\mathbb Q)$ is finitely generated for every $d\ne0$, from the
two-isogeny descent and the descent theorem with heights, so that a point of infinite order and
$\#\mathrm{Sel}_2(C_d)=8$ give every Selmer class. `docs/research/cr3-map-literature.md` §8, N2, Lean
cost (iii): a height descent for $C_d$ over $\mathbb Q$ of the kind already done for the generator
curve. `docs/research/pc-audit.md` record RK9: the counting argument that uses finite generation.

## The positive-rank form

`docs/research/cr3-map-literature.md` §0 (the cleanest narrowing) and §8, N2 (CR3^rk, the
recommended trust statement): the same premises, with the conclusion that $C_d(\mathbb Q)$ contains
a point of infinite order. This is what Kriz, Tian–Yuan–Zhang with Gross–Zagier, and finiteness of
$Ш(C_d)[2^\infty]$ each conclude; the note argues that it is equivalent to CR₃ through RK9 and
Proposition 0. Only the implication CR₃^Rk ⇒ CR₃ is proved here, not the converse.
`KERNEL_PLAN.md`, the paragraph beginning "These hypotheses all conclude": the forms CR₃^Rk,
CR₃^TYZ,Rk and CR₃^TYZ_Cl,Rk, the implications CR₃^TYZ_Cl,Rk ⇒ CR₃^TYZ,Rk (Rédei's formula) and
CR₃^TYZ,Rk ⇒ CR₃^Rk (Corollary 4.4 and Theorem 3.6), and the main-theorem variants.
`docs/research/rv-cr3-dl.md` §2.1 reviews the second implication.

## Row 5b and Redei

`docs/research/tyz-5b.md` Corollary 4.4 (a Selmer first coordinate $\beta$ with
$|\beta|_{\rm odd}\equiv3\pmod4$, in particular $|\beta|\equiv7\pmod8$, forces $\det M_{5b}=1$) and
Theorem 3.6 ($\det M_{5b}=T_{5b}(d)$ for squarefree $d\equiv5\pmod8$); `docs/research/tyz-5b.md`
§2.2 and `docs/research/redei-plan.md` for Rédei's formula, which identifies $T_{5b}(d)$ with the
genus sum of Tian–Yuan–Zhang's class numbers.

## The two curves of a slot choice

`docs/research/rv-cr3-dl.md` §1.1: pole completeness applies the rank hypothesis at exactly two
curves, $C_{d_1}$ and $C_{d_1|\theta|}=C_{d_2}$ of a slot choice. Quantifying over every triple
$\beta,\theta,p_0$ that satisfies the inputs makes the hypothesis stronger than needed. The
existential slot choice makes it weaker, which is legitimate because pole solubility holds for any
slot choice. The form over admissible inputs quantifies only over admissible $B$. §1.2: the inputs
can hold ($\beta=-7$, $\theta=1$, $p_0=7$, where a slot choice gives $d_1=7q_0$ for a prime
$q_0\equiv3\pmod8$), slot data exist whenever they hold, and no slot choice is degenerate
($d_1\ge21$, and both 2-Selmer groups have order $8$). `docs/research/cr3-map-needs.md` §1 (L4) and
§2 (W3): the proof of pole completeness applies CR₃ only at these two curves, and W3 is the drop-in
narrowing of CR₃ that keeps the construction of the descent. `KERNEL_PLAN.md`, the paragraph
beginning "The proof applies CR₃ at only two curves".

## Positive rank on the two curves

`KERNEL_PLAN.md`, the paragraph beginning "These hypotheses all conclude": RK9 (with Mordell–Weil for
$C_d(\mathbb Q)$, a point of infinite order and a 2-Selmer group of order $8$ make every Selmer class
come from a rational point) and the positive-rank forms CR₃^Rk and CR₃^TYZ,Rk; the next paragraph,
for CR₃^DL,Rk and CR₃^DL,Adm,Rk. `docs/research/rv-cr3-dl.md` §1.4 (CR₃^Rk implies CR₃^DL,Rk: the
2-Selmer group of each curve of a slot choice has order $8$ and contains a class with first
coordinate $\beta$), §2.1 (Corollary 4.4 and Theorem 3.6 give an odd genus sum $T_{5b}$) and §2.3
(the chain from these hypotheses to Tian–Yuan–Zhang's input, an odd genus sum with their own class
numbers).

## The infinitely-many-points forms

A project-authored restatement, not taken from the manuscript or from any published source:
`KERNEL_PLAN.md`, the paragraph beginning "These hypotheses all conclude", records that the four
positive-rank hypotheses CR₃^Rk, CR₃^TYZ,Rk, CR₃^TYZ_Cl,Rk and CR₃^DL,Rk are restated with the
conclusion that $y^2=x^3-d^2x$ has infinitely many rational solutions, so that the hypotheses can be
read without the group law, and that each form is equivalent to its positive-rank form through
Mordell–Weil for $C_d$ (see Mordell-Weil for the congruent number curves above). For squarefree
$d>0$ this conclusion is the classical statement that $d$ is a congruent number; that reading is
standard background and no proof here uses it.

## The literature form of CR3

`KERNEL_PLAN.md`, section "What can and cannot be formalized", the three sentences beginning
"`ZInQKernel/MainLiterature.lean` splits CR₃ further" (in the paragraph after the Lean display that
follows "CR₃ itself follows in Lean from a positive-rank statement"): CR₃ is split further into three
statements about the L-series of an elliptic curve, namely that for every elliptic curve over
$\mathbb Q$ a simple zero of $L(E,s)$ at $s=1$ gives a point of infinite order, the functional
equation of $L(C_d,s)$ with conductor $32d^2$ and root number $-1$ on the critical strip, and that
$L(C_d,s)$ vanishes to order at most one at $s=1$ when $T^{\rm Cl}_{5b}(d)=1$. The first two are
textbook theorems; the third is Tian–Yuan–Zhang's Theorem 3.5(2) in the reading that Proposition N
proves, which no refereed text prints (KERNEL_PLAN's wording). Of the texts read for this project,
only Smith's unrefereed preprint prints that reading (`docs/research/nt-tyz.md` Verdict 1 and §3:
the journal version of Tian–Yuan–Zhang and Tian's two expository articles were not read).

`docs/research/rv-lit.md`, cited first: §0 (verdict: adopt, with the functional equation restricted
to $0<\operatorname{Re}s<2$ and the Gross–Zagier statement renamed with its twist supplier
corrected); §1.2 (each adopted statement is true given its cited theorem, and none is vacuous or
trivially true); §3 (faithfulness of the Gross–Zagier statement, the functional equation and
row 5b); §6 (the adopted statements are the drafts apart from those two changes); §7 (the repairs
to the notes, including repair N1).

`docs/research/wk-cr3.md` §2.1 (the definitions: entire continuation, its uniqueness, the completed
L-function) and §2.3 (the proofs: vanishing at the centre from the functional equation at $s=1$,
analytic rank one, and CR₃^TYZ_Cl,Rk from row 5b, vanishing at the centre and Gross–Zagier);
§2.2 gives the draft statements and §3 their faithfulness table; both are superseded for the functional equation (now restricted to
$0<\operatorname{Re}s<2$) and for the Gross–Zagier statement (renamed, twist supplier corrected)
by the note at the end of wk-cr3 and by rv-lit §6 and §7 (repair N1). These are project notes, not
published sources.

## The L-series of an elliptic curve

For a Weierstrass equation $E$ over $\mathbb Q$, $L(E,s)$ is the Euler product over the primes $p$
of $f_p(p^{-s})^{-1}$, where $f_p$ is the local polynomial of a minimal model over
$\mathbb Q_p$, with Silverman's factors: $1-a_pT+pT^2$ with $a_p=p+1-\#\tilde E(\mathbb F_p)$ for
good reduction, $1-T$ for split and $1+T$ for nonsplit multiplicative reduction, and $1$ for
additive reduction. `docs/research/wk-cr3.md` §1.2 (item "The L-function") and §3 (paragraph "The
L-series definition": for odd squarefree $d$ the model $y^2=x^3-d^2x$ has $\Delta=64d^6$ and
$c_4=48d^2$, is minimal at every prime, has good reduction off $2d$ and additive reduction at $2$
and at $p\mid d$; PARI confirms conductor $32d^2$, root number $-1$, minimality and the local data
on 20 squarefree $d\equiv5\pmod8$ below 4000). `docs/research/rv-lit.md` §2 (the recipe checked by
reading for every residue characteristic, including split and nonsplit multiplicative reduction at
$2$ and $3$, and, for a transcription of that recipe (the defined series itself cannot be computed),
against PARI's coefficients up to $n=300$ on 29 curves, non-minimal models among
them, with no mismatch). No proved statement links the defined series to point counts; a mismatch
would make the literature statements false, not vacuous (`docs/research/wk-cr3.md` §3, residual
risk). The normalization is arithmetic, with centre $s=1$; the series converges
absolutely for $\operatorname{Re}s>3/2$ by Hasse's bound (STANDARD; wk-cr3 §3, rv-lit §1.1).

## Entire continuation

`docs/research/wk-cr3.md` §1.2 (item "Analytic continuation"): the order of vanishing at $s=1$ is
taken of an entire function that agrees with the series on $\operatorname{Re}s>3/2$, and such a
function is unique. `docs/research/rv-lit.md` §1.1: the half-plane is $\operatorname{Re}s>3/2$, not
$\operatorname{Re}s>1$, because on $\operatorname{Re}s>3/2$ the series converges absolutely (Hasse),
while on $\operatorname{Re}s>1$ it need not converge and no entire function need agree with it; an
entire continuation exists for every elliptic curve over $\mathbb Q$, since $E$ is modular
(Breuil–Conrad–Diamond–Taylor) and the L-function of a weight-2 newform is entire (Hecke),
and for $C_d$ by Deuring and Hecke (STANDARD), so the statements that quantify over all entire
continuations are not vacuous; and since a continuation is not identically zero, its order of
vanishing at $s=1$ is finite.

## Hecke and Deuring

$C_d$ has complex multiplication by $\mathbb Z[i]$, so $L(C_d,s)$ is the L-function of a Hecke
character of $\mathbb Q(i)$ (Deuring; Hecke), which is entire and satisfies a functional equation
(STANDARD; locators not checked). `docs/research/wk-cr3.md` §1.2 (item "Analytic continuation") and
§4.3 (proving this here would need Hecke L-functions of $\mathbb Q(i)$ and Deuring's identification
of $L(C_d,s)$; out of reach); `docs/research/rv-lit.md` §1.1 (existence of the continuation for
$C_d$) and the row for Hecke's continuation in the table of §1.2 (true, STANDARD).

## The functional equation and the root number

With $\Lambda(s)=N^{s/2}(2\pi)^{-s}\Gamma(s)L(C_d,s)$, the functional equation is
$\Lambda(2-s)=w\Lambda(s)$, with conductor $N=32d^2$ for odd squarefree $d$ and root number $w=-1$
for $d\equiv5,6,7\pmod8$: Deuring and Hecke for the functional equation, and B. J. Birch and
N. M. Stephens, Topology 5 (1966), for the sign, cited as `docs/research/cr3-trust.md` B9 cites it
(title and pages not checked here). The conductor $32d^2$ for odd squarefree $d$ is standard
(`docs/research/cr3-trust.md` §1, D1, cites Koblitz, GTM 97, Ch. II; locator not checked); it is
checked with PARI for 20 squarefree $d\equiv5\pmod8$ below 4000 (`docs/research/wk-cr3.md` §3)
and for the first 30 such $d$, from $5$ to $285$ (`docs/research/rv-lit.md` §3.2). The statement
used here is restricted to
$0<\operatorname{Re}s<2$, on which neither $s$ nor $2-s$ is a pole of $\Gamma$, and is used only at
$s=1$.

`docs/research/rv-lit.md`, cited first: §1.2 (the form for every $s$ is false at $s=0$, where the
gamma factor is taken to be $0$ while $L(C_d,2)\ne0$, with values $0.911$, $1.024$, $0.904$ for
$d=5,13,21$; on the strip the identity holds, checked numerically to $2\cdot10^{-17}$ at three
points for $d=5,13,21$) and §3.2 (PARI gives conductor $32d^2$ and root number $-1$ for the first
30 squarefree $d\equiv5\pmod8$, from $5$ to $285$; the normalization is the standard one).
`docs/research/wk-cr3.md`, the closing note (the adopted form holds on the strip only and
suffices, since the proof uses $s=1$), and its §3 row for the functional equation only as
superseded: it calls the all-$s$ draft true; see rv-lit §1.2 and its repair N1.

## Reading A of Tian-Yuan-Zhang

Theorem and proposition numbers are those of arXiv:1411.4728v1 (Theorem 3.5 is label `m3`), the
only version read; the journal version (Asian J. Math. 21 (2017)) was not read and its numbering
may differ (`docs/research/nt-tyz.md` §1.1 and the numbering warning of §3).
For $n\equiv5\pmod8$ the second sum of Tian–Yuan–Zhang's Theorem 3.5(2) has terms of two types,
$(7,3)$ and $(5,1)$, and the $(5,1)$ terms admit three readings. Reading A admits $d_1=1$, so the
blocks other than the one $\equiv5$ form any, possibly empty, partition into blocks $\equiv1\pmod8$;
the sum is then $T^{\rm Cl}_{5a}(n)$, and the theorem says that if $2^{-\rho(n)}\mathcal L(n)$ is
even then $T^{\rm Cl}_{5a}(n)$ and $T^{\rm Cl}_{5b}(n)$ are both even (their sums, with
$g(d)=\#2\mathrm{Cl}(\mathbb Q(\sqrt{-d}))$; the vault's $T^{\rm Cl}$). The printed Theorem 3.5(2) permits reading A, and their
proof of Proposition 3.4 needs it; the printed Theorem 1.2, whose last sentence selects the other
readings, is false as written (for $n=26565$ and $33117$, which have rank $3$ and so $\mathcal L(n)=0$, the
second sum under those readings is odd; nt-tyz §1.4) and is not cited
(`docs/research/nt-tyz.md` §1.3–1.4). The hypothesis "$2^{-\rho(n)}\mathcal L(n)$ even" is
replaced by the stronger hypothesis $\mathcal L(n)=0$ (so the statement is weaker than theirs), that is, order of vanishing at least two (nt-tyz §2.2, fact F6, and
§4.1). Proposition N proves reading A in this form (its first sentence) from unambiguous statements
of Tian–Yuan–Zhang (nt-tyz §4); it is unpublished, written for this project, with two model reviews (rv-nt-tyz,
rv-prop-n) and no human review. The only printed statement of reading A found is
A. Smith, arXiv:1603.08479, Theorem 2.1, with the two sums as separate rows; it is unrefereed. The
journal version of Tian–Yuan–Zhang and Tian's expository articles (Notices of the ICCM 5 (2017);
Proc. ICM 2022) were not read (nt-tyz §3; wk-cr3 §0).

`docs/research/wk-cr3.md` §1.1 (reading A is the true form; row 5a is rejected as an alternative;
the smallest gap is Lemmas N1, N2 and fact F5 of Proposition N) and the §3 rows for row 5b and for
reading A (where the $T_{5a}$ sum is called new in the draft and not reviewed; it is checked in
rv-lit §3.3, a model review only). `docs/research/rv-lit.md` §3.3: row 5b is the contrapositive of
the $T_{5b}$ half of Proposition N, weakened to order at most one, and needs the existence of the
continuation (Hecke); the $T_{5a}$ sum, with one block $\equiv5$ and the rest $\equiv1\pmod8$,
including the one-block partition, matches reading A's $T_{5a}$ by reading; an independent sample
of 30 values of $d$ (the rank-3 cases $26565$ and $33117$, and the first 28 squarefree
$d\equiv5\pmod8$ with at least two primes $\equiv3$ or $7\pmod8$) found no violation of row 5b or of
reading A.

## Kriz

D. Kriz, *Supersingular main conjectures, Sylvester's conjecture and Goldfeld's conjecture*,
arXiv:2002.04767, Theorem 10.13: the rank-one 2-converse theorem for curves with CM by
$\mathbb Z[i]$, a preprint whose publication status was not checked
(`docs/research/pc-audit.md` RK1; `docs/research/cr3-map-literature.md` §4, C4;
`docs/research/rv-lit.md` N2). With the corank lemma (see the Route K locators,
Cassels-Tate) it gives $\operatorname{rank}C_d(\mathbb Q)=1$ when $\dim\mathrm{Sel}_2(C_d)=3$. Its
construction assumes $f_0\ge4$, where $f_0$ is the odd part of $|d|$; for odd squarefree
$d\equiv5\pmod8$ this holds, since $f_0=d\ge5$ (RK1). It is an alternative route that the
hypotheses do not need (`docs/research/nt-tyz.md` §5.1).

## Tian-Yuan-Zhang

Y. Tian, X. Yuan, S.-W. Zhang, *Genus periods, genus points and congruent number problem*, Asian J.
Math. 21 (2017), no. 4, 721–774; arXiv:1411.4728. Theorem 3.5 and the argument of the proof of
Theorem 3.5(2), §3.3, as completed in `docs/research/nt-tyz.md` §4, Proposition N: for squarefree
$n\equiv5\pmod8$ with odd genus sum $T_{5b}(n)$, $L(C_n,s)$ vanishes to order exactly one at $s=1$
(`docs/research/cr3-map-literature.md` §4, C2). Their genus class number is
$g(n)=\#2\mathrm{Cl}(\mathbb Q(\sqrt{-n}))$ (§1).
The literature section states Theorem 3.5(2) for $n\equiv5\pmod8$ in reading A with both sums,
with hypothesis $\mathcal L(n)=0$ (see Reading A of Tian-Yuan-Zhang above). Row 5b uses only the
$(7,3)$ sum, in contrapositive form: if $T^{\rm Cl}_{5b}(n)$ is odd then $\mathcal L(n)\ne0$. By
their definition $\mathcal L(n)=0$ exactly when $L(C_n,s)$ vanishes to order greater than one at
$s=1$ (TYZ L318–345, nt-tyz I7, as cited in `docs/research/wk-cr3.md` §1.2). For order one the
definition uses a regulator, and so presupposes the rank part of the Birch–Swinnerton-Dyer
conjecture in analytic rank one, which they cite from Coates–Wiles, Rubin, Gross–Zagier and
Kolyvagin (`docs/research/cr3-trust.md` B9).
Theorem, lemma and section numbers here and in Reading A of Tian-Yuan-Zhang are those of
arXiv:1411.4728v1; the journal version was not read and its numbering may differ
(`docs/research/nt-tyz.md` §1.1, the numbering warning in §3, and §5.2 item 2).

## Gross-Zagier

B. Gross and D. Zagier, *Heegner points and derivatives of L-series*, Invent. Math. 84 (1986),
225–320, applied with an auxiliary imaginary quadratic field that satisfies the Heegner hypothesis
and has $L(C_d^K,1)\ne0$ (Bump–Friedberg–Hoffstein). `docs/research/cr3-trust.md` §1, D2 names
the suppliers: Bump–Friedberg–Hoffstein, Waldspurger, or Friedberg–Hoffstein, not Murty–Murty (the
derivative case); their theorem numbers, and whether the level $32d^2$ is allowed, are still to be
checked. Only "analytic rank one implies rank at least one" is used;
Kolyvagin's finiteness of $Ш$ is not needed, and $C_d$ is modular since it has CM by $\mathbb Z[i]$
(`docs/research/pc-audit.md` RK7).
The literature section states the positive-rank half for every elliptic curve over $\mathbb Q$:
a simple zero of $L(E,s)$ at $s=1$ gives a point of infinite order. Modularity is
Breuil–Conrad–Diamond–Taylor, J. Amer. Math. Soc. 14 (2001) (Shimura 1971 for CM curves); the
auxiliary twist comes from Bump–Friedberg–Hoffstein, Invent. Math. 102 (1990) (through
Waldspurger) or Friedberg–Hoffstein, Ann. of Math. 142 (1995); Kolyvagin, Math. USSR Izv. 32
(1989), adds that the rank is exactly one, which is not used (STANDARD: these texts were not read here; their theorem numbers, and the
hypotheses on the level under which the auxiliary field exists, are unchecked for every conductor,
not only for $32d^2$) (`docs/research/rv-lit.md` §3.1;
`docs/research/wk-cr3.md` closing note; `docs/research/cr3-trust.md` §1, D2-D3).

## Silverman-Tate

J. H. Silverman and J. Tate, *Rational Points on Elliptic Curves*, Undergraduate Texts in
Mathematics, Springer (1992). Chapter I, §4: the explicit formulas for the group law (the chord
through two points, the tangent at one, and the third intersection with the cubic). Chapter III,
for the curves $y^2=x^3+ax^2+bx$ and $y^2=x^3-2ax^2+(a^2-4b)x$: the two-isogeny between them and the homomorphism $\alpha$ to
$\mathbb Q^\times/\mathbb Q^{\times2}$ (§4); Mordell's theorem, where the index of $2\Gamma$ is
bounded by the sizes of the images of $\alpha$ and $\bar\alpha$, which lie in the classes of the
divisors of $b$ and of $a^2-4b$ (§5); and finite generation from the height lemmas (§§1–3). No
project note cites this book, and the chapter and section numbers were not checked.

## Silverman, descent and heights

J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Springer (2009): the descent theorem
for an abelian group with a height (Theorem VIII.3.1); heights on elliptic curves over number
fields, with the naive height, the approximate parallelogram law and the finiteness of points of
bounded height (§VIII.6); descent via two-isogeny for $y^2=x^3+ax^2+bx$ (Proposition X.4.9). No
project note cites these numbers, and they were not checked.
