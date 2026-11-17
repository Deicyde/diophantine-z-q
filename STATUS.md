# Z is Diophantine in Q: status of the Lean formalization (2026-11-16)

The manuscript *Z is Diophantine in Q* (November 5, 2026; `diophantine_zq.pdf` in
https://github.com/elliotglazer/diophantine-z-q) constructs one polynomial P with integer coefficients such that a rational number q is an integer exactly when
P(q, w) = 0 for some tuple w of rational numbers. This project checks that proof in the Lean 4 proof assistant,
with the Mathlib library.

- Upstream: since 2026-11-13 the Lean kernel is on the main branch of https://github.com/elliotglazer/diophantine-z-q
  (pull request #36 merged #24's kernel, with CI checks for contributions)
- Development fork: https://github.com/Deicyde/diophantine-z-q (Lean state of fork main c0f3d085, which adds proofs of
  two of the headline's five hypotheses, a reduction of Gross–Zagier to two narrower statements from the literature
  and a theorem of Shimura, a reduction of reading A (the reading of a theorem of Tian, Yuan and Zhang that the proof
  uses; item 4 below) to four statements drawn from published results, among them the same theorem of Shimura, and a
  proof of H from 29 theorems from the literature, with no glue statement left; a single Lean theorem,
  `ZInQ.OneProof.frozenTarget`, states the whole proof with exactly the open statements as its hypotheses)
- Start here to help: https://github.com/Deicyde/diophantine-z-q/issues/14 explains how to pick an open statement,
  claim it and prove it; docs/one-proof/OPEN.md lists every open hypothesis with its Lean statement, its kind, its
  source and who is working on it
- Blueprint, with every statement, its dependencies and its Lean declaration: https://deicyde.github.io/diophantine-z-q/

The open statements of the current proof (generated from docs/one-proof/OPEN.md; counts elsewhere in this file
describe the fork main they name):

<!-- open-count:begin -->
**32 hypotheses of the H part** (in the bundles `OpenAddedLeaves25`, `OpenResearchLeaves39`, `OpenTextbookLeaves16`), plus 5 hypotheses of the Tian–Yuan–Zhang and Gross–Zagier parts listed at the end of docs/one-proof/OPEN.md.

* **Strict count: 14 published / 18 glue** (the strictest flagged reading; no hypothesis carries a strictest-reading flag).
* By kind: composite 3, consequence 6, published 23.
* Generated from docs/one-proof/OPEN.md by scripts/one_proof/render_open.py.
<!-- open-count:end -->

## Status in three lines

- **Proved in Lean, with no gaps:** the manuscript's Theorem 1.1, in exactly the form frozen upstream, follows
  from two inputs: H, a height bound (the manuscript's Theorem 4.1), and a positive-rank statement for certain
  congruent number curves.
- **Reduced in Lean:** the positive-rank statement follows from four statements about L-functions, and two of them,
  the functional equation and Hecke's continuation, are now proved in Lean (on the development fork; upstream pull
  request #114, which supersedes #64, proposes them together with the rest of the fork's proof). The other two are
  Gross–Zagier, a published theorem combined with standard results, and one reading of a theorem of Tian, Yuan and
  Zhang that no refereed text we found states explicitly (caveats below). On the fork, Lean reduces Gross–Zagier to
  statements from the literature, and two of them remain: clause (ii) of a theorem of Bump, Friedberg and Hoffstein on
  the nonvanishing of central twisted values, as printed for newforms on Γ₀(N), and the Gross–Zagier formula over the
  algebraic modular curve X₀(N), for the curves isogenous to C_d; with them the proof uses Shimura's main theorem of
  complex multiplication, and Lean proves the rest (among it that the theta series of the Hecke character of C_d is a
  newform, the q-expansion principle for Γ₀(N), and Gross's conjugation relation). Lean also reduces this reading,
  reading A, to four statements: three from the work of Tian, Yuan and Zhang and Shimura's theorem, as printed. The
  two classical theorems on ternary quadratic forms that they cite (Legendre's three-square theorem and a theorem of
  Jones and Pall) and three more of their statements, hypotheses until now, are proved in Lean. Three of the four are
  printed theorems or special cases of them; the remaining one, their Theorem 3.3 in the form the proof states,
  reaches the printed theorem only through the analytic uniformization.
- **Open, and most of the remaining work:** H. In Lean, H now follows with no gaps
  (`HDec.HSyn.sixContactMin_of_open48`, the H part of `ZInQ.OneProof.frozenTarget`) from 29 theorems from the
  literature that are still open, in six bodies of published mathematics (Shimura curves, abelian varieties, Néron
  models and semistable reduction, Faltings heights, p-adic Hodge theory, and Galois representations of modular
  forms); no glue statement is left. Of the 29, 13 are published statements (some specialized or weakened), 11 are
  consequences of published theorems, and 5 are candidates: composites of published results that are not printed in
  this form. The strict convention also leaves out a published statement whose reading against the print is recorded
  as pending: under it, 11 of the 29 count as published statements and 18 do not, and the strictest reading gives the
  same count. A dictionary pass on 2026-11-16 re-rated the statements against their printed forms. Statement reviews
  by AI models of earlier leaves found none stronger than its source, with two caveats: the leaf for Pazuki's height
  bound may state it more strongly than he prints it, by about log 4, depending on a normalization not yet checked
  against his paper, and the displayed constant of Bost's bound has not been read. Two leaves added since carry a
  recorded risk of exceeding the print under one reading of it (Raynaud's criterion and SGA 7 IX 3.3). No human has
  checked the leaves.

So what remains for H is to prove these 29 theorems, several of them major results; the positive-rank side still needs
the four statements behind reading A and the two Gross–Zagier statements (Shimura's theorem serves both). These are
exactly the hypotheses of `ZInQ.OneProof.frozenTarget` (`ZInQKernel/OneProof/Main.lean`). Folding in a proof of a
hypothesis removes it from that theorem.

## How far to trust each part

| Part | Status |
| --- | --- |
| The construction of P and every finite computation about it (variables, degree, coefficients) | proved in Lean, no hypotheses |
| Theorem 1.1 from H and the positive-rank statement | proved in Lean |
| The positive-rank statement from items 1 to 4 below | proved in Lean |
| Items 2 and 3: the functional equation and Hecke's continuation | proved in Lean on the development fork, not yet upstream |
| Item 1: Gross–Zagier | a published theorem combined with standard results; assumed (on the fork, reduced to two statements from the literature and a theorem of Shimura, with the rest proved) |
| Item 4: Tian–Yuan–Zhang, reading A | not printed in this form in any refereed text we found; assumed (on the fork, reduced to four statements drawn from published results) |
| H, the manuscript's Theorem 4.1 (one instance) | unrefereed; its new arguments reviewed only by AI models; assumed |
| H from 29 open theorems from the literature (24 research-level, 3 textbook, 2 introduced by the project's reductions) | proved in Lean on the development fork, in the module chain `ZInQKernel/OneProof/H/` (built with `ZInQKernel/OneProof/Main.lean`, outside the library target) |
| Theorem 1.1 from exactly the statements that are still open | proved in Lean on the development fork (`ZInQ.OneProof.frozenTarget`) |

"Proved in Lean" means the Lean kernel checked it, with no `sorry` (unproved step), no `native_decide` (trusted
external evaluation), and only the standard axioms `propext`, `Classical.choice`, `Quot.sound`. "Assumed" means stated
in Lean as a proposition and passed as a hypothesis, never as an axiom. On the development fork three of the
headline's hypotheses remain: H, Gross–Zagier and reading A; there Gross–Zagier is further reduced to two narrower
statements from the literature and a theorem of Shimura, and reading A to four statements drawn from published
results, among them the same theorem. `ZInQ.OneProof.frozenTarget` proves `ZInQ.FrozenTarget` from exactly the
statements that are still open: the 29 leaves of H's assembly, the four statements behind reading A, and the two
Gross–Zagier statements. Everything else is machine-checked, so a reader needs to trust only those statements, not the
rest of the manuscript's argument. Upstream's headline still lists all five until the two proofs, proposed in pull
request #114 (which supersedes #64), are merged there.

## The statement checked

`ZInQ.FrozenTarget` says: there is a polynomial P with integer coefficients in 292,890,231,905 variables, of total
degree below 2↑↑7 and with every coefficient below 2↑↑8 in absolute value, such that a rational number q is an
integer if and only if P(q, w) = 0 for some tuple w of 292,890,231,904 rational numbers. Here 2↑↑n is a tower of n
twos (2↑↑1 = 2 and 2↑↑(n+1) = 2^(2↑↑n)). `scripts/check_target.py` confirms that this statement is textually
identical, up to whitespace, to upstream's frozen statement of Theorem 1.1 in `lean/Frozen/BoundedIntegerPolynomial.lean`.

The headline Lean theorem is
`ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzThm35ReadingA_heckeContinuation_functionalEquation5_grossZagier`
(`ZInQKernel/MainLiterature.lean`); its name lists its five hypotheses, and upstream's CI registers each of them as a
target (`KERNEL_CONTRACT.json`). On the fork, `ZInQ.Contrib.functionalEquation5` and `ZInQ.Contrib.heckeContinuation`
prove two of them, with exactly the registered names and types, and
`ZInQ.Contrib.GaussFE.frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagier`
(`ZInQKernel/Contrib/GaussFE/Headline.lean`) proves `ZInQ.FrozenTarget` from the other three.
`ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner`
(`ZInQKernel/Contrib/GZTheta/NewCMFinal.lean`) proves it from H, reading A, `ZInQ.GZDecomp.FHNonvanishing` and
`ZInQ.GZDecomp.GrossZagierHeegner`, and
`ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd`
(`ZInQKernel/Contrib/GZStatements/Weak.lean`) from forms of the last two restricted to the curves C_d, and
`ZInQ.Contrib.TYZChain.frozenTarget_of_sixContactMin_grossZagier_tyzChainLeaves`
(`ZInQKernel/Contrib/TYZChain/Headline.lean`) from H, Gross–Zagier and the four statements of the first reduction of
reading A (see "Reduction of item 4" below). `ZInQ.OneProof.frozenTarget` (`ZInQKernel/OneProof/Main.lean`) proves it
from the leaves of H's assembly, the four statements behind reading A, and the two Gross–Zagier statements, and from
nothing else. Other variants, listed in README.md, take other forms of the positive-rank statement, for example
`Literature.TYZRow5b` in place of items 3 and 4.

## The hypotheses

### Positive rank

The construction needs a rational point of infinite order on the congruent number curve C_d: y² = x³ − d²x for
every squarefree d ≡ 5 (mod 8) whose genus sum T5bCl(d) is odd. Here T5bCl(d) ∈ Z/2 is the sum, over the set
partitions of the primes of d with one block ≡ 7, one block ≡ 3 and all other blocks ≡ 1 (mod 8), of the products
over the blocks B of #2Cl(Q(√−d_B)), the order of the subgroup of squares in the class group, where d_B is the
product of the primes in B; T5aCl(d) is the same sum over the partitions with one block ≡ 5 and all others ≡ 1
(mod 8). Lean derives this positive-rank statement from four statements over Mathlib's L-series of an elliptic
curve (`WeierstrassCurve.LSeries`):

1. `Literature.GrossZagier`: if an analytic continuation of L(E, s) has a simple zero at s = 1, then E(Q) has a point
   of infinite order, for every elliptic curve E over Q. This is Gross–Zagier (1986) with an auxiliary quadratic twist
   (Bump–Friedberg–Hoffstein 1990) and modularity (Breuil–Conrad–Diamond–Taylor 2001), not one printed sentence. The
   proof needs it only for C_d with d ≡ 5 (mod 8) squarefree, and on the fork
   `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves` replaces it by three statements: that the
   theta series of the Hecke character of C_d is a newform (Hecke, Shimura), the nonvanishing of central twisted
   values (Friedberg–Hoffstein, Bump–Friedberg–Hoffstein), and Gross–Zagier with Gross's conjugation relation, with
   all the glue proved (docs/research/gz-decomp.md). The first of the three is now proved
   (`ZInQ.GZTheta.heckeThetaNewform`), with Hecke's theorem for y² = x³ − x and the Atkin–Li theorem that a quadratic
   twist of a newform is new at the expected level (`ZInQ.GZTheta.atkinLiTwistNew`) proved too
   (docs/research/gz-theta.md, docs/research/atkin-li.md), so the remaining hypotheses are
   `ZInQ.GZDecomp.FHNonvanishing` and `ZInQ.GZDecomp.GrossZagierHeegner`. A statement review by AI models found
   neither stronger than the published theorem it cites, provided Friedberg–Hoffstein's theorem has the generality the
   review recalls (not yet checked against the paper); Lean also derives the frozen statement from weaker forms of the
   two, restricted to the curves C_d, and proves that the restricted Gross–Zagier statement follows from
   `Literature.GrossZagier` (docs/research/gz-statements.md). In `ZInQ.OneProof.frozenTarget`,
   `ZInQ.GZDecomp.FHNonvanishing` is replaced by clause (ii) of the opening theorem of Bump, Friedberg and Hoffstein
   (Invent. Math. 102 (1990)), as printed at weight 2 for the classical newforms on Γ₀(N), with the Kronecker symbol
   (`ZInQ.BFHPrinted.BFHClauseIIGamma0`), from which Lean derives it with no twisted root number; Lean proves that
   these newforms are the newforms of trivial character of the vendored Tau Ceti library (docs/research/bfh-gamma0.md,
   bfh-kronecker.md, bfh-leaf.md). It counts as a published statement. An AI model has compared it with the paper
   clause by clause, and no human has read it against the paper; under Diamond and Shurman's definition of a newform,
   rather than the Atkin–Lehner one, one step of that comparison is not proved. `ZInQ.GZDecomp.GrossZagierHeegner`, in
   its form for the curves C_d, is now derived from the Gross–Zagier formula over the algebraic modular curve X₀(N),
   for optimal parametrizations of the curves isogenous to C_d (`ZInQ.GZAlg.GrossZagierAlgOptCd`), from Shimura's
   theorem (which replaces the fourth statement of the reduction of item 4, below), and from three statements now
   proved in Lean: the q-expansion principle for Γ₀(N), the transformation law of the eta quotient
   η(8τ)η(32τ)²/η(16τ)³ under Γ₀(32), and Gross's conjugation relation (docs/research/gzopt-dict.md, etaw32-proof.md).
   The formula counts as a published statement whose reading is pending: three steps between Gross and Zagier's
   morphism from X₀(N) to the curve and its Lean form, through the pull-back of functions, are not proved in Lean, so
   the strict convention does not count it as published.
2. `Literature.FunctionalEquation5`: for squarefree d ≡ 5 (mod 8), the functional equation of L(C_d, s) with
   conductor 32d² and root number −1 (Deuring, Hecke; Birch–Stephens 1966), stated on the strip 0 < Re s < 2,
   which avoids the points where Mathlib's Gamma function takes the conventional value 0; a textbook consequence.
   **Proved in Lean** on the fork (`ZInQ.Contrib.functionalEquation5`).
3. `Literature.HeckeContinuation`: for every positive integer d, L(C_d, s), defined by its Euler product for
   Re s > 3/2, extends to an entire function (Deuring, Hecke: C_d has complex multiplication by Z[i]); standard.
   **Proved in Lean** on the fork (`ZInQ.Contrib.heckeContinuation`).
4. `Literature.TYZThm35ReadingA`: for squarefree d ≡ 5 (mod 8), if L(C_d, s) vanishes to order at least 2 at
   s = 1, then T5aCl(d) and T5bCl(d) are both even. This is Theorem 3.5(2) of Tian–Yuan–Zhang (arXiv:1411.4728v1;
   Asian J. Math. 21 (2017)) for n = d, in one reading of its genus sums ("reading A": the decompositions of n are
   set partitions of its primes, each counted once, with a trivial factor allowed), and it is needed only when
   their invariant 𝓛(n) is 0, which happens exactly when the order of vanishing at s = 1 is at least 2. That case
   is a special case of the printed hypothesis.

How they combine: the functional equation with root number −1 makes L(C_d, s) vanish at s = 1; when T5bCl(d) is
odd, items 3 and 4 bound the order of vanishing by 1 (this is the statement `Literature.TYZRow5b`, which the Lean
theorem `Literature.tyzRow5b_of_readingA` proves from them); so the zero is simple, and item 1 gives a point of
infinite order. Items 2 and 3 are proved in Lean from Gauss's count (1814) of the points of y² = x³ − x over
finite fields, which is proved in Lean too, through theta series over Z[i] and Mathlib's functional-equation pairs
(docs/research/gauss-proof.md, docs/research/hecke-all.md).

**Caveats on item 4.** No refereed text found by the project's literature search (carried out by AI agents)
states reading A explicitly; the one statement found (Smith, arXiv:1603.08479, Theorem 2.1) is unrefereed. TYZ's
introductory theorem with the same parity criteria (Theorem 1.2 of the arXiv version, Theorem 1.4 of the journal
version) requires every factor to exceed 1, and read that way it is false in both versions: d = 26565 and
d = 33117 are counterexamples (exact class-group computations and explicit points of rank at least 3, not checked
in Lean). Read the same way, Theorem 3.5(2) is false too; reading A, which the project uses, is consistent with
both values and with all 32 cases in a scan of squarefree n ≡ 5 (mod 8) below 52000 of analytic rank 3
(docs/research/nt-tyz.md, section 1.4). The paper's proof of Theorem 3.5(2) passes through its Proposition 3.4,
whose proof is only a sketch in the arXiv version; the journal's proof was not assessed on this point. The
comparison of the two versions was made by AI agents with web access; no human has checked it.

**Supporting evidence, not a hypothesis of the headline.** `TYZRow5b` and `TYZThm35ReadingA` are also proved in
Lean from `PropN.TYZInputs`, which encodes consequences of results printed in the arXiv version together with two
standard facts TYZ use without printing (one of them Hecke's continuation, now proved); the encoding's faithfulness
has been checked only by AI models. The Lean proof follows a new argument, Proposition N (docs/research/nt-tyz.md,
section 4), that AI models reviewed twice and no human has reviewed. Conversely, Lean proves that reading A
implies `PropN.TYZInputs` given Hecke's continuation (`ZInQ.Contrib.PSide.tyzInputs_iff_readingA_of_hecke`), so
the encoding is exactly as strong as item 4. 

**Reduction of item 4 (on the fork).** `ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_leaves`
(`ZInQKernel/Contrib/TYZChain/Main.lean`, docs/research/tyz-chain.md) derives item 4 from four statements drawn from
published results. Two concern the invariant 𝓛(m) of Tian, Yuan and Zhang, whose square is L(C_m, 1) divided by a real
period and a power of 2: that 𝓛(m) is an integer for squarefree m ≡ 1 or 3 (mod 8) (the first assertion of Theorem 1.1
of arXiv:1411.4728v1, for odd m), and their Lemma 2.9 combined with their Proposition 2.3, modulo 2. The third is
their Theorem 3.3 with Lemma 3.14, for the CM points that the project fixes; they do not print the computation behind
the constant of Theorem 3.3, which docs/research/tyz-t1.md writes out and checks numerically. In
`ZInQ.OneProof.frozenTarget` the third is replaced by their Theorem 3.3 as printed, for n ≡ 5, 7 (mod 8)
(`ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33`): Lean derives the form above from it, and Lemma 3.14, whose conclusion is
the first sentence of the printed theorem, is no longer a separate hypothesis (docs/research/tyz-split.md). The fourth
is the main theorem of complex multiplication for the values of rational modular functions on X₀(N) at Heegner points
(`Shimura.ShimuraReciprocityModFn`; Shimura 1971, Thm 5.4, with the canonical model of X₀(N)), which a review by AI
models found to follow from Shimura's theorem. In `ZInQ.OneProof.frozenTarget` it is replaced by Shimura's theorem,
which enters in Weierstrass coordinates (`T5Glue.ShimuraMainCM`, now derived from the printed form, below): the proof
uses the fourth statement only at level 32, for the two coordinates of the eta-quotient model of X₀(32), and there
Lean derives it from Shimura's theorem and an identity between theta functions and the Weierstrass function that is
now proved in Lean (`ThetaWeierstrass8`; docs/research/hx-used.md, theta-wp8.md). In `ZInQ.OneProof.frozenTarget` the
second statement is replaced by six published statements, from which Lean derives it
(`H29Split.tyzLemma29Mod2_of_sixLeaves`; the derivation and four of the six statements use the finite adeles and class
groups of the vendored Tau Ceti library; docs/research/h29-split.md, h29-fix.md, h29-ne3.md): Legendre's three-square
theorem; the theorem of Jones and Pall that the form x² + y² + 16z² represents every squarefree n ≡ 1 (mod 8); and
four statements of Tian, Yuan and Zhang, each restricted to the cases the proof uses: the existence of a nonzero test
vector (their section 2.1), their Lemma 2.9 as printed for n ≠ 3, their Theorem 2.1 for (d₁, d₂) = (3, 1), and their
Proposition 2.3 as printed. Five of the six are now proved in Lean, and only their Lemma 2.9 remains a hypothesis:
Legendre's theorem (fork pull request #36, with the three-square theorem of the atlas-lean library, vendored with its
notice), the theorem of Jones and Pall (fork pull request #38), their Theorem 2.1 at (3, 1), from the class number 1
of Q(√−3), a computation with Brandt matrices checked by the kernel, and certified bounds on two L-values
(docs/research/t21-proof.md), the existence of a nonzero test vector, by computations checked by the kernel, with a
Hurwitz approximation from fork pull request #39 (hfx-proof.md), and their Proposition 2.3 (hp23-proof.md). In the
arXiv version (the journal version was not checked), Lemma 2.9 as printed is false at n = 3, by an exact computation
of AI models that no human has checked (docs/research/h29-fix.md): its display omits the factor w_K of Theorem 2.1,
from which their proof derives it, and w_K is 3 for Q(√−3) and 1 for the other fields Q(√−n) that the proof uses
(squarefree n > 1), so the instance of Theorem 2.1 covers n = 3. Their printed proof that 𝓛(m) is an integer also
passes through that display at n = 3; the integrality statement still holds there: numerically, 𝓛(3) = ±1. The first
is a special case of a printed statement; the printed form of the third now counts as a consequence of the print,
since its Lean statement uses the eta-quotient model of X₀(32) where Tian, Yuan and Zhang use an algebraic
isomorphism, and only the analytic uniformization identifies the two; the second and the fourth combine published
results; the one statement still open among the six that replace the second is a printed statement restricted to the
cases the proof uses; and Shimura's theorem, which replaces the fourth, now enters as printed: his Theorem 5.4 for an
analytic isomorphism of C/𝔞 with the complex points of an elliptic curve, restricted to short Weierstrass models and
without its uniqueness clause (`ZInQ.Contrib.HCMDict.ShimuraThm54`), from which Lean derives the form in Weierstrass
coordinates (docs/research/hcm-dict.md); it counts as a published statement, and no human has read it against the
book. All four are stated over concrete Lean definitions, with no bundled existential statement
(docs/research/tyz-decomp.md, cm-points.md). Lean proves the rest of the route: 𝓛(1) = 1; their Lemma 3.18 on torsion,
in the form the project states, for every squarefree n ≡ 5 (mod 8) (docs/research/tyz-318.md, sqrt2-glue.md); and, for
the genus points built from the fixed CM points, their Lemma 3.21(1) and the case 𝓛(n) = 0 of the unnumbered first
assertion of their Theorem 3.5 (the point P(n) of their recursion is then torsion). No human has compared the
statements of this reduction with their sources: AI models found the first two of the four faithful and no stronger
than the paper (docs/research/tyz-lcal.md, which lists the passages a human should still read, among them the
normalization of 𝓛), and compared the statements for the fixed CM points with the paper. AI models wrote the six
statements that replace the second from the arXiv version, citing it line by line (docs/research/h29-ne3.md); Jones
and Pall's paper was not read, and their statement is now proved in Lean. The Lean statement of the printed Theorem
3.3 fixes one convention: a sign in the CM points that the project fixes for n ≡ 5 (mod 8) (with the other sign the
statement would be false, not weaker). The sign was first chosen from numerical checks of Theorem 3.3
(docs/research/tyz-t1.md, section 3.1); a later review by AI models found that the paper fixes the same sign, in the
proof of its proposition on the Hecke action for n ≡ 5 (mod 8) (docs/research/tyz-split.md, section 2.2). That review
assumes that the kernel's analytic parametrization of X₀(32) is the one defined over Q, which has not been checked.

### H, the six-contact height estimate

`ZInQ.SixContactMin` (`ZInQKernel/Hypotheses/HeightMin.lean`): for every rational u outside the six contact values
{0, −15, −20, −24, −30, −60}, h(u) ≤ H₆(D) · M(u)²⁴. Here h(a/b) = log max(|a|, b) is the logarithmic height of
a/b in lowest terms; M(u) is the product of the primes p outside a fixed finite set at which v_p(u − c) is
positive and odd for some contact value c; and H₆(D) is an explicit constant (`ZInQKernel/Hypotheses/Height.lean`).
It is the one instance of the manuscript's Theorem 4.1 that the proof uses. H is not a published theorem: the
proof of Theorem 4.1 combines refereed theorems and exact computations with new arguments, the manuscript's and
this project's, that only AI models have reviewed (docs/research/h-trust.md).

## What is proved in Lean with no hypotheses

The construction of the polynomial and every finite computation about it run in the kernel. The manuscript used
several further inputs that are no longer hypotheses:
- the twenty-two-prime pattern is replaced by Green–Tao (Vasily Ilin's Apache-2.0 Lean proof, vendored and
  extended to dense subsets of the primes) together with a density statement for the good primes, proved with
  Mathlib's Chebyshev bounds and a Selberg sieve vendored from the PrimeNumberTheoremAnd project;
- Mordell–Weil for the generator curve and the catalogue bound (by an effective Dirichlet theorem) are proved;
- pole completeness is proved from the positive-rank statement.

On the positive-rank side, Lean proves Rédei's formula, the identification of Mathlib's L-series of C_d with the
classical one, the reduction of the positive-rank statement to items 1 to 4, and Proposition N from the encoded
inputs `PropN.TYZInputs`. On the fork it also proves Gauss's point count, items 2 and 3, the newform statement of
item 1 with the Atkin–Li theorem (docs/research/atkin-li.md), the basic facts about the coefficients of L(C_d, s)
(multiplicativity and the recursion at prime powers, a_p = 0 for p ≡ 3 (mod 4), Hasse's bound, absolute
convergence for Re s > 3/2) and the equivalence of the encoded inputs with reading A (docs/research/p-side.md).

## What is left: the decomposition of H

docs/research/h-decomposition.md breaks H into **leaves**, theorems from the literature that are stated in Lean and
assumed until someone proves them, and **glue**, the arguments that connect them, which the project must prove in
Lean. On the manuscript's route H follows from 23 research-level theorems (Shimura and Deligne on the level-3 Shimura
curve of discriminant 6, Baba–Granath, Lin–Yang, Igusa, González–Rotger, Raynaud, Serre–Tate, Grothendieck, Faltings
1983 twice (semisimplicity and the Tate conjecture; the Faltings height under isogeny), de Rham comparison, Berger,
Pan's Fontaine–Mazur theorem, Saito or Kato, Deligne, Deligne–Serre, Shimura on J₁(N), Carayol, Javanpeykar,
Gaudron–Rémond, Bost, Pazuki, and the theorem that the stable Faltings height is finite and attained by Néron models),
35 textbook theorems (among them the existence of Jacobians and of Néron models, the dimension of J₁(N), the analytic
uniformization of abelian varieties, and five facts about elliptic curves and function fields from which X₁(N) and its
Belyi map are built), and 20 glue steps. The project's assemblies split these steps into smaller named statements and
prove them one by one; the canonical assembly, below, needs none. Its leaves differ from the manuscript's list: some
leaves are split into several statements, some textbook theorems are proved, and the project's reductions add new
ones.

- **The top theorem.** `HDec.HSyn.sixContactMin_of_open48` (`ZInQKernel/OneProof/H/TailZ55.lean`) proves
  `ZInQ.SixContactMin`, the kernel's own statement of H, from 29 named hypotheses, none of them a placeholder: 24
  research-level leaves (from the 23 research-level theorems, some split into several statements, some replaced by
  published statements from which Lean derives them; others of the 23, among them Baba–Granath, Lin–Yang, Igusa and
  Faltings on the height under isogeny, are now proved or no longer needed, and one, Bosch, Lütkebohmert and Raynaud's
  existence theorem for Néron models over a Dedekind domain, comes from the textbook list), 3 textbook leaves, and 2
  leaves that the project's reductions introduced; no glue statement is left. Of the 29, 13 are published statements,
  some of them specialized or weakened; 11 are consequences of published theorems; and 5 are candidates. A leaf counts
  as published only in its printed form or as a direct instance of it, a special case that needs no argument; a leaf
  whose Lean form takes a theorem to reach from the print, such as a passage through the analytic uniformization or
  through GAGA, counts as a consequence; and the strict convention leaves out a published leaf whose reading against
  the print is recorded as pending (the rules that docs/one-proof/OPEN.md states; its section "Kernel-wide readings"
  records the readings that apply to every statement built on a shared kernel definition). Under the strict
  convention, 11 of the 29 hypotheses count as published statements and 18 do not: the 11 consequences, the 5
  candidates, and 2 published leaves whose reading is pending (SGA 7 IX 3.3 and 3.5 over a strictly henselian base).
  The strictest reading gives the same count. docs/one-proof/OPEN.md, generated from the build, lists the 29
  hypotheses with their Lean statements, kinds, sources and who is working on each, and docs/one-proof/kinds.tsv gives
  each rating with its source; they are the fields of the structures `OpenResearchLeaves31` (`TailZ50.lean`),
  `OpenTextbookLeaves16` (`TailZ50.lean`) and `OpenAddedLeaves25` (`TailZ55.lean`); the number in each name counts
  generations of the bundle, not fields. The blueprint's chapter on the decomposition
  (blueprint/roadmap/height-decomposition/, generated from the build by scripts/one_proof/vault_chapter/gen.py) states
  each of the 29 in informal mathematics, grouped by the theory it comes from: Shimura curves of discriminant 6;
  abelian varieties; Néron models, semistable reduction and monodromy; Faltings 1983 and Faltings heights; p-adic
  Hodge theory; and Galois representations of modular forms. Section 3 of docs/research/leaf-fold9.md first grouped
  the leaves of an earlier assembly this way.
  The glue statement of earlier assemblies, `HeckeVertWitness` (one unramified vertical prime above each prime p > 324
  in the Hecke cover, equivalent to the project's Lemma NV), is now proved along the steps of Lemma NV, from
  statements that the assembly derives from its leaves (among them the moduli description of the Shimura curve Y₃,
  Mumford's description of torsion points and Elkies' coordinate on the quotient of X₆ by its Atkin–Lehner group). Its
  third step, `NVLocalInertia`, the one glue statement of the previous status (if E is a finite Galois extension of
  Q(X) of degree less than p whose finite branch points lie in a set S of rational numbers that are p-integral and
  distinct modulo p, and b is a point of S above which the residue fields of E are unramified at p, then every inertia
  element at a prime above pZ[X] is conjugate to an element of an inertia group above X − b), is now proved, from
  Abhyankar's lemma over a discrete valuation ring and Zariski–Nagata purity in dimension 2, both proved earlier, with
  no new hypothesis (docs/research/nv-local.md, abhyankar.md).
  The assembly folds in a check of earlier candidates (docs/research/leafq-check.md), the splitting of many leaves
  into the published statements they follow from (docs/research/av-split.md, curve-split.md, hodge-split.md,
  qm-split.md, height-split.md), and proofs of the height glue and of a covolume step for the group Γ* (the
  normalizer of the quaternion order, acting on the upper half-plane) (docs/research/height-glue.md, qm-glue.md).
  Since the status of 2026-11-14 (fork main b5ff0474), the folds described in docs/research/leaf-fold14.md and in the
  task reports named here (all under docs/research/) have changed the assembly. They prove outright Bosch,
  Lütkebohmert and Raynaud's 1.2, Proposition 4 (gt-blr.md), EGA IV 8.10.5 for open immersions (gt-ega.md), that
  Igusa's theta expressions ψ₄ and χ₁₀ are Siegel modular forms (gt-theta.md), Shimizu's covolume of the norm-one
  group of the quaternion order and the valence formula for a cocompact Fuchsian group (gt-gamma.md, gt-valence.md),
  and the étaleness of multiplication on an abelian scheme (below); and they prove the description of the
  endomorphisms of a QM abelian surface over C that commute with the quaternion order from textbook leaves already
  present (gt-qm.md). The five results of SGA 7 IX that were then counted as consequences over a discrete valuation
  ring were then derived from printed statements of SGA 7 IX over a strictly henselian base, with Bosch, Lütkebohmert
  and Raynaud's theorem that Néron models commute with strict henselization (1.2, Proposition 2; since derived from
  their 7.2, Theorem 1, below) (reduct-b.md, gt-sga7.md, gt-unip.md, gt-shpair.md). Two hypotheses that the proof
  carried without needing them, Fontaine's computation of the Galois invariants of B_dR and Raynaud's bound on the
  correction term of Faltings' Lemma 5, are gone, and so is Yu's Theorem 1.1, whose consumers now use a form proved
  from other leaves (sem-prune.md, yu-prune.md). Other leaves are replaced by printed or narrower statements: the
  moduli leaf of the Shimura curves Y₃ and X₆ and the conic model of X₆ by statements drawn from published theorems of
  Deligne, Baba and Granath, González and Rotger, and Elkies, with González and Rotger's count of CM points now in its
  printed form, their Proposition 5.6 (x6-fold.md, gt-grcount.md, gt-elkies.md); the existence of a symmetric isogeny
  on every abelian variety by four statements on the Picard scheme and the Weil pairing (t09-pic.md); the rigidity
  leaf (Theorem 6.14 and Corollary 6.4 of Mumford's Geometric Invariant Theory) by Theorem 6.14 alone (gt-rigidity.md,
  rigid-prune.md); Shimura's holomorphic family and the ray-class form of his reciprocity law by one leaf, his Main
  Theorem I in Deligne's form (gt-rayclass.md); the good reduction of Y₃ by the representability of its moduli problem
  over Z_(p) (sgr-split.md); and Shimura's theorem on the abelian varieties attached to newforms (R16) by the same
  statement without its rank-two clause, which is now proved from two textbook leaves (r16-split.md).
  Since the status of 2026-11-15 (fork main 862bd440), H has lost twelve hypotheses and gained one; the task reports
  named here are under docs/research/. The folds prove outright the irreducibility of X₀(N) (below), so that Igusa's
  theorem on the Galois image of N-torsion is no longer needed (flt-cqj2.md); the inequality that the proof uses from
  Faltings' Lemma 5, from the kernel's definition of the height (faltings5-lower.md); and the half of Stacks, Tag
  00TV, that the proof uses (a finite-type algebra over a perfect field is smooth near a prime at which its local ring
  is regular), from a lemma of the vendored Jacobian-Challenge library (below) and Mathlib (fork pull request #24).
  They prove from leaves already present Shimura and Taniyama's theorem in the form the proof uses (a QM abelian
  surface over C with complex multiplication by Z[i], Z[ζ₃] or Z[√−6] comes from an abelian variety over Q̄;
  st-qbar.md); Baba and Granath's rational coordinate on the quotient of X₆ by its Atkin–Lehner group, with the CM
  points of discriminants −4, −3 and −24 over three distinct rational values (bg-explicit.md); the first assertion of
  SGA 7 IX 3.3 over a strictly henselian base, from its second assertion and three other leaves (persists-dvr.md); and
  the connectedness of the Shimura curve Y₃, the one consequence the proof drew from Deligne's description of its
  components, from Theorem 6.14 of Mumford's Geometric Invariant Theory and Shimura's Main Theorem I in Deligne's
  form, with the Artin map of the vendored Tau Ceti library (dcy3-used.md). Bosch, Lütkebohmert and Raynaud's
  existence theorem for Néron models over an arbitrary discrete valuation ring is no longer assumed: the proof uses it
  only for the discrete valuation rings of number fields, where it follows from the textbook leaf over rings of
  integers by Bosch, Lütkebohmert and Raynaud's 1.2, Proposition 4, on the localization of Néron models, proved
  outright above (neron-dvr.md, r6-nf.md). Two leaves on the connected components of X₆, Deligne's description and a
  criterion for geometric connectedness, are gone: they supported only the statement that X₆ is geometrically
  connected, which no step of the proof uses (pi0-fold.md). The integral model of Y₃ over Z_(p) and the quotient
  coordinate on it are gone too: the one step that used them is now proved by another route, with one new glue
  statement, since proved (above; sgr-direct.md, sgr-fold.md). Elkies' theorem now enters in what the project takes to
  be his own wording, the equality of function fields ℚ(X₆)^W = ℚ(t), not yet read against his paper
  (elkies-coord.md), and Diamond and Shurman's Theorem 9.6.5 as the disjunction of its two possible wordings (the
  characteristic polynomial of Frobenius is the Hecke polynomial, or Frobenius satisfies it), which either wording
  gives directly (ds965-weak.md; since replaced by its printed form, below). Three of the four leaves on the Picard
  scheme and the Weil pairing (t09-pic.md) were then counted as consequences rather than published statements: the
  printed theorems concern Mumford's dual abelian variety over an algebraically closed field, and reaching the Lean
  statements, about the Picard scheme of an abelian variety over any field, takes identification and descent steps (a
  statement review of 2026-11-16).
  Since the status of 2026-11-16 (fork main 0caafe66, with the Lean of 2880fef1), the combined fold leaf-fold32 has
  removed nineteen hypotheses of H and added eleven; the task reports named here are under docs/research/. It proves
  the last glue statement (above); four textbook leaves, by fork pull requests: that a connected scheme of finite type
  over a field with a rational point is geometrically connected (#25, from proof sources of AxiomMath's Stacks
  library), that the irreducible components of a group scheme of finite type over a field all have its dimension
  (#31), Cartier's theorem that a group scheme locally of finite type over a field of characteristic 0 is smooth
  (#34), and the analytic uniformization of every complex abelian variety (#35); and four leaves that the project's
  reductions had introduced: the Ax–Sen–Tate theorem and Tate's vanishing of the Galois invariants of the twists of
  C_p (#29, from Anthropic's Lean formalization of Fermat's Last Theorem), the quasi-inverse of an isogeny
  (milne-compile.md), and EGA IV 8.10.5 (xii), by which properness spreads out from a limit (ega-limit.md, from
  vendored files of AxiomMath's Stacks library). The leaf on the algebraicity of theta-constant ratios is no longer
  needed: its one use is proved with no hypotheses (theta-direct.md, theta-fold2.md); and SGA 3 VI_B 3.10 is narrowed
  to its neighbourhood form (gt-sga3.md). The dictionary pass re-rated the statements against their printed forms
  (kinds.tsv gives the reason for each re-rating in the row's flag), and where a printed form could be written down
  the statement was restated and the step to the old one proved in Lean: Bosch, Lütkebohmert and Raynaud's 7.2,
  Theorem 1 (Néron models commute with base change of ramification index 1 with separable residue extension), from
  which their 1.2, Proposition 2 now follows; SGA 7 IX 3.3 with its open subscheme as printed; Raynaud's criterion,
  with either reading of semistable reduction; Theorem 6.14 of Mumford's Geometric Invariant Theory over a connected
  base (dict-models.md); the criterion of Néron–Ogg–Shafarevich over a separable closure (dict-galois.md); two
  statements of Mumford over an algebraically closed field, the finiteness of K(L) and the surjectivity of φ_L, in
  place of the statement that φ_L is an isogeny (pic-dict.md, pic-fix.md); Diamond and Shurman's Theorem 9.6.5 as
  printed, over the completion of the coefficient field, with the statement that the coefficients of an eigenform
  generate a number field, which the theorem presupposes (coeff-ext.md); and Deligne and Serre's Theorem 4.1 as
  printed (coeff-fix.md).
  The next fold, leaf-fold33 (docs/research/leaf-fold33.md lists its steps and checks), removed ten more hypotheses of
  H and added two. It proves Bosch, Lütkebohmert and Raynaud's 7.2, Theorem 1 outright (neron-sh-proof.md), Poincaré's
  complete reducibility from other leaves (poincare-proof.md), and, from the leaves on the Picard scheme, the
  finiteness of K(L) (leaf-fold33.md, step 7) and the Weil pairing (phisurj.md). The statement that the identity
  component of the Picard scheme of an abelian variety is an abelian variety, which the proof needs only in
  characteristic 0, is replaced in that case by three printed statements, of which two are now proved (that the Picard
  scheme is locally of finite type, and that the identity component of a group scheme locally of finite type over a
  field is an open subgroup that is geometrically irreducible) and one remains, Kleiman's theorem that the identity
  component of the Picard scheme of a proper geometrically normal scheme is proper (piczero-char0.md, idcomp-lft.md,
  piclft.md). Theorem 6.14 of Mumford's Geometric Invariant Theory and the existence of Néron models over rings of
  integers are both replaced by Bosch, Lütkebohmert and Raynaud's existence theorem for Néron models over a Dedekind
  domain (goodmodel-iso.md). The uses of the homomorphism theorem for abelian varieties over an algebraically closed
  field, of SGA 3 VI_B 3.10 and of the surjectivity of φ_L are rerouted to proofs that do not need them
  (leaf-fold33.md, sga3-nbhd.md, phisurj.md); a reroute keeps the original declarations and carries a copy of the
  chain that reads them.
  The six height leaves of earlier assemblies (R18 to R22 and the finiteness of the stable height) are now theorems,
  derived, with the analytic uniformization of abelian varieties (T35) and the existence of Néron models, from
  statements from the literature: Bost's lower bound, Javanpeykar's bound, Pazuki's bound, the theorem of Gaudron and
  Rémond, and the results on semistable reduction and Néron models above; the inequality that they use from Faltings'
  Lemma 5 is now proved (faltings5-lower.md).
  The proof of `CoarseFactor` (docs/research/coarse-factor.md) is part of the assembly: it is a glue step in the
  derivation of the moduli description of Y₃ and X₆, and of the conic model of X₆, from published-form leaves.
- **Statement review.** AI models reviewed the 62 leaves of an earlier assembly, many of which are still among the
  current ones (docs/research/leaf-review-a.md, docs/research/leaf-review-b.md): 8 are published statements and 54 are
  consequences of published statements, each with its derivation written out; none is stronger than its source. No
  human has reviewed them. The reviews list the assumptions they rest on, among them a lemma fixing the principal
  polarization of a QM abelian surface whose published locators are unverified, a check of the Shimura curve's moduli
  problem that still needs a human, and the definition of the stable Faltings height. Section 2 of
  docs/research/leaf-fold7.md and of leaf-fold8.md flags twenty leaves for a human check. Six of them are still
  hypotheses; one of the six, Diamond and Shurman's Theorem 9.6.5, now enters as printed, over the completion of its
  coefficient field, and the convention it was flagged for, the way its coefficients are carried from C to the ℓ-adic
  field, is now proved in Lean (docs/research/coeff-ext.md). Seven are now proved (Igusa's ψ₄ and χ₁₀, Lin and Yang's
  Igusa invariants at discriminant −24, the valence formula, the analytic uniformization, the geometric connectedness
  of a connected scheme of finite type with a rational point, and the equidimensionality of group schemes); four are
  derived from other leaves, in the forms the proof uses (Shimura's holomorphic family; the moduli leaf R1R2fpRep,
  without its clause that X₆ is geometrically connected; Yu's Theorem 1.1; and Shimura and Taniyama's theorem); the
  question about Raynaud's criterion passes to the statement that replaced it (SGA 7 IX 4.7 over a strictly henselian
  base, now with either reading of semistable reduction); and the questions about Faltings' Lemma 5 and the good
  reduction of the Shimura curve are moot, since the inequality that the proof uses from the lemma is now proved and
  the proof no longer uses that good reduction. The check of an earlier assembly's candidates found none of them false
  and none true only for a trivial reason. A review of the height leaves (docs/research/height-split.md, section 8)
  raised three risks. One is an open question: if the level-2 theta coordinates in Pazuki's paper are the second-order
  ones, the leaf for his bound (`pazukiCor13Upper`, which replaced R22) states it about log 4 more strongly than he
  prints it, and whether the argument tolerates the weaker constant has not been checked. The displayed constant of
  Bost's bound is unread: the leaf takes the weaker of the two usual normalizations and would be slightly stronger
  than the print only under a third. The third, the wording of Faltings' Lemma 5, no longer matters: the one
  inequality that the assembly uses from the lemma is now proved in Lean from the kernel's definition of the height,
  with no hypothesis (docs/research/faltings5-lower.md).
- **Citations.** An audit of the citations against the primary sources by AI agents with web access
  (docs/research/locators.md) corrected several theorem and example numbers, and the corrections are applied.
  Some locators, among them Faltings 1983, Serre–Tate, SGA 7, Bost's constant and Shimura 1967, are still
  unverified (the audit lists them all).
- **Repairs.** Reviews on 2026-11-12 found three leaves misstated, and all three are repaired on the fork's main
  (upstream's main still has the first statement of Yu's dichotomy): the González–Rotger count of CM points now
  carries the factor 2^b(R) (the step that uses it holds with the correct count); the Lean statement of Yu's QM
  dichotomy (a textbook leaf) now includes Yu's hypothesis that the quaternion algebra is indefinite (as first
  written it was stronger than published); and the branching data of the Atkin–Lehner quotient is reworded. On
  2026-11-13, R14 (Galois representations of eigenforms) was found to omit its published determinant clause, and
  the proof of G8-G12 uses a form of R14 that includes it; an input of step G4 was found false as stated and was
  replaced by a corrected form, proved from two leaves; and R10 (de Rham comparison) was found to lack the clause
  of the Hodge–Tate decomposition that the manuscript's appendix lemma needs. The amended R10 includes it, and
  the appendix lemma (G9) now follows from the amended R10 alone.
- **Textbook leaves proved** since 2026-11-12: Skolem–Noether, Brauer–Nesbitt in characteristic 0, Herbrand's theorem,
  Abhyankar's lemma, the local square-root criterion (from local Kronecker–Weber), Kronecker–Weber, local
  Kronecker–Weber (part (a)), Chebotarev's theorem (finite form), the global forms of Hilbert's different formula and
  of the different bound, the existence of a newform with the eigenvalues of a Hecke eigenform, the computation of
  local `H²(G_{ℚ_v}, ℤ/2)` in cochain form, the vanishing of unramified local classes, Brauer–Hasse–Noether with
  reciprocity for `H²(G_ℚ, ℤ/2)`, the structure of the N-torsion of an elliptic curve, good reduction implying
  unramified torsion over k(T), the Clebsch–Bolza–Igusa separation of binary sextics by their Igusa invariants, the
  equality of the dimension of the Jacobian of a curve with its genus (docs/research/dimjac-glue.md), and, since the
  status of 2026-11-16, by fork pull requests, the geometric connectedness of a connected scheme of finite type with a
  rational point (#25), the equidimensionality of group schemes of finite type over a field (#31), Cartier's
  smoothness theorem in characteristic 0 (#34) and the analytic uniformization of complex abelian varieties (#35); the
  freeness of Tate modules (T26) now follows from T5, which the canonical assembly derives from Mumford's description
  of the torsion of an abelian variety over an algebraically closed field. Most of these proofs are under
  `ZInQKernel/Contrib/`, and many use the class field theory and modular forms of the Tau Ceti library (Apache-2.0),
  which is vendored there (its license and notice files are in `ThirdParty/TauCeti/`, and the vendored files that were
  modified carry the change notices that Apache-2.0 §4(b) asks for, as a script checks). The project proved six more
  leaves of earlier assemblies, all now dropped from the canonical one: the surjective half of the Néron mapping
  property for abelian schemes, T11(b) (a rigidity theorem for abelian varieties), the twist of an eigenform by a
  character (T24), Zariski's connectedness theorem, and EGA IV 8.8.2(ii) and 17.7.8(ii). Four of these rest on outside
  Apache-2.0 Lean code, vendored with its license and notice files, to which the project added bridges: the Néron
  proof and the affine Noetherian input to Zariski's theorem come from Anthropic's Lean formalization of Fermat's Last
  Theorem (which includes material from Imperial College London's FLT project), and the two EGA IV statements from
  AxiomMath's Stacks library; T11(b) adapts a rigidity proof from AxiomMath's Mordell library, and T24 uses Tau Ceti's
  twists of cusp forms. They also proved three more, which the canonical assembly folds in: T33, the existence of the
  Jacobian of a curve with a rational point, with its Albanese property, over every field, from the Lean library
  frenzymath/Jacobian-Challenge (copyright Axel Delaval, Jie Xu and Shitan Xu, with parts adapted, per its notice,
  from Weil's conjectures project; Apache-2.0), vendored under `ZInQKernel/Contrib/`; the normal model of a function
  field of one variable over Q (Stacks, Tag 0BXX); and the étaleness of multiplication by an integer invertible on the
  base, for an abelian scheme over any base (fork pull request #19), which reuses proof sources from AxiomMath's
  Stacks library (Apache-2.0), vendored with its license and notice under `ZInQKernel/Contrib/MulEtale/`.
  Zariski–Nagata purity is now proved in the form the proof uses (over a regular base of dimension at most 2), in the
  assembly's modules. The rational cusp of X₁(N) now follows from `X0Transitive` (X₀(N) is irreducible: the Galois
  group of ℚ(j) permutes the cyclic subgroups of order N of the generic elliptic curve transitively), which is now
  proved, from the bijection between the cyclic quotients of the generic elliptic curve and the roots of the modular
  polynomial in Anthropic's Lean formalization of Fermat's Last Theorem (which includes material from Imperial College
  London's FLT project; Apache-2.0, vendored with its license and notice files), so Igusa's theorem that this Galois
  group acts on the N-torsion through all of GL₂(Z/N) is no longer a hypothesis (docs/research/flt-cqj2.md); Zariski's
  connectedness theorem, which replaced an earlier, less standard leaf, is now proved. The canonical assembly also
  derives T9 and Serre's lemma from other leaves, replaces T6, T7 and T41 by weaker published statements, proves
  T11(b) and the weaker form of T3 that it uses (the Néron mapping property for abelian schemes), and splits T34 and
  T38 into general statements about curves over Q, all of which are now proved or no longer needed, among them T38's
  rational-point clause (docs/research/av-b1.md, av-b2.md, curves-g.md, curve-split.md, neron-c.md, leaf-fold5.md).
- **Proved glue.** Every glue step of the canonical assembly is proved from the leaves, with no `sorry`, in the
  kernel-checked library under `ZInQKernel/HDecomp/` and `ZInQKernel/Contrib/` or in the assembly's modules under
  `ZInQKernel/OneProof/H/`. Among them: `HeckeVertWitness`, from leaves alone (docs/research/sgr-direct.md,
  nv-local.md, abhyankar.md); the height glue (the analytic uniformization and the metrization of the Hodge line); the
  passage from the norm-one units of the quaternion order to Γ* (an index-4 covolume computation); the step G4 (the
  Hom field), from leaves alone; the adelic bookkeeping of the normalizer of the quaternion order, with |Γ'| = 144,
  over Mathlib's finite adeles; the model of X₁(N) over Q and its Belyi map; the Galois representation of a newform as
  a subrepresentation of the Tate module of J₁(N), its semisimplicity and continuity, and its comparison with two
  other Galois representations; the whole last stretch of the glue (from the level bound, the theta point and the
  height inequalities to H); the manuscript's Brauer and cochain steps; good reduction of the abelian surface away
  from 3; absolute irreducibility and the nonzero homomorphism step; the trace comparison; the conductor bound; the
  core of G10 (the conjugate twist is nontrivial); the count of inner twists and the unramified conjugates; the field
  of the kernel at step G4; the base change of abelian varieties and the multiplication isogeny, from Mathlib alone;
  the appendix lemma (G9), from the amended R10 alone; the comparison of two moduli maps (`MobiusGlue`), from one
  textbook leaf; the Kummer step of Proposition TS; the curve charts of the Hecke covers, including their properness
  and quasi-finiteness; the Galois descent of twists; the base change of the Hodge line, of the invariant
  differentials and of complex points; the uniqueness of the Hauptmodul that the period map uses (`hauptmodulUnique`,
  with a certified numerical evaluation of a theta value); the period map; and the spreading out of an abelian variety
  over a number field, from three statements of EGA IV, all three now proved.
- **Still missing from every Lean library:** the definitions that section 4 of docs/research/h-decomposition.md lists.
  None of them is behind a placeholder any more: conductors of ℓ-adic representations are defined, and the complex
  uniformization of the Shimura curve is stated concretely in family form. Mathlib cannot yet construct a nonzero
  abelian variety; on the fork, Jacobians of curves with a rational point now exist in the library, from the vendored
  Jacobian-Challenge library above, and their dimension is now proved to be the genus (`DimJacobianEqGenus`). The
  height leaves of the canonical assembly are stated over Lean definitions of semistability and of the stable Faltings
  height (docs/research/height-split.md); that these agree with the published definitions is a judgement of AI
  reviews, and Lean has checked their non-vacuity only in the trivial case of the zero abelian variety.
  Dimension theory (the dimension of an integral variety is the transcendence degree of its function field, and
  the local rings of a smooth variety at its closed points are regular of the expected dimension), and the absolute Frobenius of a scheme of
  characteristic p are now in the library, under `ZInQKernel/Contrib/Dim/` and `ZInQKernel/Contrib/AbsFrob/`.
- **Fallback route.** An alternative modularity route (Khare–Wintenberger with Ribet) needs 20 research-level
  theorems; one adversarial model review, and no human, found it sound subject to five repairs that are not yet
  written, and whether Ribet's 1992 proceedings paper was refereed is unchecked.

## How to help

Start at https://github.com/Deicyde/diophantine-z-q/issues/14, which a coding agent can follow as written to prove
exactly the Lean statement of an open hypothesis and open a pull request against the fork's main, where the proof
is folded into `ZInQ.OneProof.frozenTarget`. docs/one-proof/OPEN.md lists every open
hypothesis of that theorem with its exact Lean statement, its kind, its source and who is working on it;
CONTRIBUTING.md is the guide for contributors, and docs/one-proof/CONTRIBUTING.md the short contract for a proof,
which `#discharges` checks.
Claim a statement before starting, in one place: comment `Claiming <field> at <commit>` on
https://github.com/Deicyde/diophantine-z-q/issues/14 (older claims on the upstream topic issues stay valid). To check a
statement against its printed source without Lean, see docs/one-proof/STATEMENT-CHECKS.md. The tracking issue
https://github.com/elliotglazer/diophantine-z-q/issues/37 lists the open-target issues (one per topic), the
definitions to build, the leaves, the open glue, and the pull requests that already prove some of the targets.
Of upstream's five registered targets, two have proofs on the fork (`ZInQ.Contrib.heckeContinuation`,
`ZInQ.Contrib.functionalEquation5`), proposed upstream in pull request #114 (which supersedes #64), and three are open:
`ZInQ.Contrib.sixContactMin` (H), `ZInQ.Contrib.tyzThm35ReadingA` and `ZInQ.Contrib.grossZagier`.
Pull requests to upstream go to the main branch of https://github.com/elliotglazer/diophantine-z-q. A merge currently
requires the required checks to pass on a branch that is up to date with main, with every review thread resolved.
Among them are the complete kernel build and exact-target audit, the accepted Lean helpers and axiom audit, and
`Protocol B / review`: under upstream's Protocol B, active since 2026-11-13, both approved model reviewers must
finish and accept every mathematical change (docs/research-review/README.md upstream). The live ruleset
(https://github.com/elliotglazer/diophantine-z-q/rules/26781429) shows what a merge currently requires; CI alone
does not establish that an argument is correct. The open statements are grouped as upstream issues, one per topic, listed in the
tracking issue; they follow the rows of revision r5 of docs/research/frontier.md, which listed the open statements as they would
have stood at fork main 28b41fb3 if every reduction then compiled on the fork were folded in; several of those
reductions are now folded in, and https://github.com/Deicyde/diophantine-z-q/issues/14 has the current list.
`ZInQ.OneProof.frozenTarget` (`ZInQKernel/OneProof/Main.lean`) takes exactly the open
statements as hypotheses: a proof of one is folded in by replacing that hypothesis with the proof. The status column of docs/one-proof/OPEN.md shows who
holds each statement. To build and check: `lake exe cache get`, then
`lake build ZInQKernel`; then `lake env lean scripts/print_axioms.lean` (every declaration listed must depend only on
the three standard axioms) and `python3 scripts/check_target.py`.

## Verification

Every Lean change is built before it reaches main. At fork main 5e235a40, the last landing that the
repository's full chain checked (leaf-fold33, on fork main since, passed the full chain on its intermediate states
through c7fbc273, and each of its steps ran the OneProof build, the axiom check of `ZInQ.OneProof.frozenTarget` and
the blueprint check; docs/research/leaf-fold33.md):
- the library build completes, all 542 declarations listed in `scripts/print_axioms.lean` (the
  headline and its variants, the reductions, the Proposition N lemmas, and the glue lemmas of the decomposition
  of H) depend only on the three standard axioms, with no `sorry`, and `scripts/check_target.py` confirms the
  statement;
- all 4,239 Lean files under `ZInQKernel/Contrib/` build (no error), most of them vendored libraries (Tau
  Ceti, the Jacobian-Challenge library, the atlas-lean three-square theorem, and parts of Anthropic's Lean
  formalization of Fermat's Last Theorem, of AxiomMath's Stacks library and of the openai/math repository, each
  with its license and notice), and the axiom reports of `scratch/contrib-check/Check.lean`, among them the two proofs of hypotheses, the headline
  variants above and the route to reading A, list only the standard axioms, with no `sorry` (to repeat this:
  `lake build $(git ls-files 'ZInQKernel/Contrib/*.lean' | sed 's#[.]lean$##; s#/#.#g')` builds every file by name,
  while `lake build ZInQKernel.Contrib.AllContrib` builds only the closure of that aggregate module; then
  `lake env lean scratch/contrib-check/Check.lean`);
- `scratch/h-decomposition/Leaves.lean` compiles cleanly;
- `lake build ZInQKernel.OneProof.Main` completes, and `#print axioms ZInQ.OneProof.frozenTarget`
  lists only the three standard axioms, so nothing it depends on uses `sorry`; the earlier assemblies' files
  compiled the same way when they were made;
- the site builds with no problems (180 pages, at fork main c0f3d085); the blueprint check passes on the commit
  that adds this status (772 articles, 2,333 dependencies, every Lean name resolved).

An independent machine re-checked an earlier snapshot proposed for upstream pull request #24 (before Proposition N):
9,923 jobs, 80 declarations with standard axioms, and an audit replay of 33,548 declarations with 0 open statements.
These checks run on the project's own machines; on the fork, GitHub Actions also runs the discharge check on each pull
request that adds a contribution (CONTRIBUTING.md), and on the upstream repository, the kernel build with an
exact-target audit is among the checks required on every pull request to main (since #36).

## Where the details are

- README.md (its account of the library dates from 2026-11-12, before items 2 and 3 were proved): the library's headline, every
  hypothesis with its sources and caveats, and the library's variant theorems; the fork's newer variants are listed
  above under "The statement checked".
- `ZInQKernel/OneProof/Main.lean`: the whole proof in one theorem, `ZInQ.OneProof.frozenTarget`, whose hypotheses
  are exactly the open statements.
- docs/one-proof/OPEN.md: every open hypothesis of `ZInQ.OneProof.frozenTarget`, with its Lean statement, kind,
  source and status, and the rule for counting a statement as published; docs/one-proof/kinds.tsv: the rating of
  each; CONTRIBUTING.md and docs/one-proof/CONTRIBUTING.md: how to prove one and check it.
- docs/research/leaf-fold14.md and the task reports named under "The top theorem" above: the folds since the
  status of 2026-11-14; docs/research/leaf-fold11.md: the assembly of that status and the steps that led to it;
  docs/research/leaf-fold10.md: the one before, with each of its hypotheses (section 2); docs/research/leaf-fold9.md:
  an earlier one, with the leaves grouped by theory (section 3) and the reductions it did not fold in (section 5);
  docs/research/leaf-fold7.md and leaf-fold8.md: earlier assemblies, with the leaves they flag for a human check.
- docs/research/leaf-review-a.md, docs/research/leaf-review-b.md: the statement review of the leaves.
- docs/research/h-decomposition.md: the original decomposition of H into leaves (section 2) and glue steps
  (section 3), the missing definitions (section 4), work packages for contributors (section 5), and risks
  (section 6); its leaf lists and glue counts predate the newer assemblies.
- docs/research/frontier.md (revision r9, of fork main 0e70c94e): the open statements on the path to
  `ZInQ.FrozenTarget` if every reduction then compiled on the fork were folded in.
- docs/research/gz-decomp.md, docs/research/gz-theta.md, docs/research/atkin-li.md, docs/research/gz-statements.md:
  the reduction of Gross–Zagier, the proof of the newform statement, and the review of the two remaining statements;
  docs/research/bfh-gamma0.md, with bfh-kronecker.md and bfh-leaf.md: clause (ii) of Bump, Friedberg and
  Hoffstein's theorem in place of the nonvanishing statement.
- docs/research/tyz-chain.md: the reduction of reading A to four statements, with their Lean text;
  docs/research/h29-split.md, h29-fix.md and h29-ne3.md: the second of them from six published statements, five of
  them now proved (t21-proof.md, hfx-proof.md, hp23-proof.md and fork pull requests #36 and #38);
  docs/research/tyz-split.md: Theorem 3.3 in printed form, and the sign convention it depends on;
  docs/research/hx-used.md and theta-wp8.md: Shimura's theorem in Weierstrass coordinates in place of the fourth
  statement, and the proof of the identity `ThetaWeierstrass8`;
  docs/research/sqrt2-glue.md: the proof of the torsion lemma; docs/research/tyz-decomp.md and
  docs/research/cm-bridge.md: the earlier steps.
- docs/research/h-trust.md: the proof of Theorem 4.1 step by step, with every supplier and its review status.
- docs/research/gauss-proof.md, docs/research/hecke-all.md, docs/research/p-side.md: the Lean proofs of items 2
  and 3 and of the facts about the coefficients of L(C_d, s).
- docs/research/locators.md: the audit of the literature citations against primary sources.
- KERNEL_PLAN.md (from 2026-11-12, before items 2 and 3 were proved and before `ZInQ.OneProof.frozenTarget`): how the
  library is organized in Lean, and how to build and check it.
- The blueprint site above: every statement with its dependencies and its Lean declaration; its chapter
  blueprint/roadmap/height-decomposition/ states the 29 hypotheses of H in informal mathematics.

## Glossary

- **Kernel-checked / proved in Lean:** accepted by Lean's kernel, with no `sorry` and only the axioms `propext`,
  `Classical.choice`, `Quot.sound`.
- **Hypothesis (assumed):** a Lean proposition passed as an argument to a theorem; nothing is added as an axiom.
- **Frozen statement:** upstream's quarantined copy of Theorem 1.1 in `lean/Frozen/`, which the project must not change.
- **Positive-rank statement:** a point of infinite order on C_d for every squarefree d ≡ 5 (mod 8) with T5bCl(d) odd.
- **Leaf:** a theorem from the literature, stated in Lean over genuine definitions and assumed until proved.
- **Candidate leaf:** a leaf that combines several published results and is not printed in this form.
- **Placeholder:** a leaf that cannot yet be stated because its definitions are missing; it carries no content.
- **Glue:** an argument connecting leaves, which the project must prove in Lean.
