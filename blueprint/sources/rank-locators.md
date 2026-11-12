# Locators for the positive-rank chapter

The positive-rank step is not in the manuscript. It is record RK9 of the project-authored audit
note `docs/research/pc-audit.md`; the positive-rank forms of the hypothesis follow the narrowing N2
of the project-authored note `docs/research/cr3-map-literature.md`; and the form on the two curves
of a slot choice is reviewed in the project-authored note `docs/research/rv-cr3-dl.md`, with the plan
`KERNEL_PLAN.md`. These are notes written for this project, not published sources. The standard
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

## Kriz

D. Kriz, *Supersingular main conjectures, Sylvester's conjecture and Goldfeld's conjecture*,
arXiv:2002.04767, Theorem 10.13: the rank-one 2-converse theorem for curves with CM by
$\mathbb Z[i]$, an unrefereed preprint (`docs/research/pc-audit.md` RK1;
`docs/research/cr3-map-literature.md` §4, C4). With the corank lemma (see the Route K locators,
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

## Gross-Zagier

B. Gross and D. Zagier, *Heegner points and derivatives of L-series*, Invent. Math. 84 (1986),
225–320, applied with an auxiliary imaginary quadratic field that satisfies the Heegner hypothesis
and has $L(C_d^K,1)\ne0$ (Bump–Friedberg–Hoffstein). `docs/research/cr3-trust.md` §1, D2 names
the suppliers: Bump–Friedberg–Hoffstein, Waldspurger, or Friedberg–Hoffstein, not Murty–Murty (the
derivative case); their theorem numbers, and whether the level $32d^2$ is allowed, are still to be
checked. Only "analytic rank one implies rank at least one" is used;
Kolyvagin's finiteness of $Ш$ is not needed, and $C_d$ is modular since it has CM by $\mathbb Z[i]$
(`docs/research/pc-audit.md` RK7).

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
