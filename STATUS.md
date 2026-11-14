# Z is Diophantine in Q: status of the Lean formalization (2026-11-14)

The manuscript *Z is Diophantine in Q* (November 5, 2026; `diophantine_zq.pdf` in
https://github.com/elliotglazer/diophantine-z-q) constructs one polynomial P with integer coefficients such that a rational number q is an integer exactly when
P(q, w) = 0 for some tuple w of rational numbers. This project checks that proof in the Lean 4 proof assistant,
with the Mathlib library.

- Upstream: since 2026-11-13 the Lean kernel is on the main branch of https://github.com/elliotglazer/diophantine-z-q
  (pull request #36 merged #24's kernel, with CI checks for contributions)
- Development fork: https://github.com/Deicyde/diophantine-z-q (Lean state of fork main 71dc3f1b, which adds
  proofs of two of the headline's five hypotheses, a reduction of Gross–Zagier to two narrower statements from the
  literature, and a proof of H from 65 theorems from the literature and one glue statement that is still to be
  proved)
- Blueprint, with every statement, its dependencies and its Lean declaration: https://deicyde.github.io/diophantine-z-q/

## Status in three lines

- **Proved in Lean, with no gaps:** the manuscript's Theorem 1.1, in exactly the form frozen upstream, follows
  from two inputs: H, a height bound (the manuscript's Theorem 4.1), and a positive-rank statement for certain
  congruent number curves.
- **Reduced in Lean:** the positive-rank statement follows from four statements about L-functions, and two of
  them, the functional equation and Hecke's continuation, are now proved in Lean (on the development fork;
  pull request #64 proposes the proofs upstream). The other two are Gross–Zagier, a published theorem combined
  with standard results, and one reading of a theorem of Tian, Yuan and Zhang that no refereed text we found states
  explicitly (caveats below). On the fork, Lean reduces Gross–Zagier to three statements from the literature and
  proves the first of them (the theta series of the Hecke character of C_d is a newform), so two remain: the
  nonvanishing of central twisted values (Friedberg–Hoffstein, Bump–Friedberg–Hoffstein) and Gross–Zagier with
  Gross's conjugation relation.
- **Open, and most of the remaining work:** H. In Lean, H now follows with no gaps
  (`HDec.HSyn.sixContactMin_of_open4`) from 65 theorems from the literature that are still open, in nine bodies of
  published mathematics (Shimura curves, abelian varieties, Néron models, Faltings heights, p-adic Hodge theory,
  Galois representations of modular forms, and others), and one glue statement, `HeckeVertWitness`, a step of the
  project's own argument that it must still prove. Seven of the 65 are candidates: composites of published
  results that are not printed in this form. A statement review by AI models found every leaf it checked to be a
  published statement or a consequence of one, none stronger than its source; no human has checked them.

So what remains for H is to prove these 65 theorems from the literature, several of them major results, and the
one glue statement; the positive-rank side still needs reading A and the two Gross–Zagier statements.

## How far to trust each part

| Part | Status |
| --- | --- |
| The construction of P and every finite computation about it (variables, degree, coefficients) | proved in Lean, no hypotheses |
| Theorem 1.1 from H and the positive-rank statement | proved in Lean |
| The positive-rank statement from items 1 to 4 below | proved in Lean |
| Items 2 and 3: the functional equation and Hecke's continuation | proved in Lean on the development fork, not yet upstream |
| Item 1: Gross–Zagier | a published theorem combined with standard results; assumed (on the fork, reduced to two statements from the literature, with the glue and the newform statement proved) |
| Item 4: Tian–Yuan–Zhang, reading A | not printed in this form in any refereed text we found; assumed |
| H, the manuscript's Theorem 4.1 (one instance) | unrefereed; its new arguments reviewed only by AI models; assumed |
| H from 65 open theorems from the literature (26 research-level, 19 textbook, 20 introduced by the project's reductions) and one glue statement | proved in Lean, in `scratch/leaf-fold4/Leaves4.lean` (checked separately from the library build) |

"Proved in Lean" means the Lean kernel checked it, with no `sorry` (unproved step), no `native_decide` (trusted
external evaluation), and only the standard axioms `propext`, `Classical.choice`, `Quot.sound`. "Assumed" means
stated in Lean as a proposition and passed as a hypothesis, never as an axiom. On the development fork three
of the headline's hypotheses remain: H, Gross–Zagier and reading A, and there Gross–Zagier is further reduced to two
narrower statements from the literature. Everything else is machine-checked, so a reader needs to trust only those
statements, not the rest of the manuscript's argument. Upstream's headline still lists all five until the two
proofs, proposed in pull request #64, are merged there.

## The statement checked

`ZInQ.FrozenTarget` says: there is a polynomial P with integer coefficients in 292,890,231,905 variables, of total
degree below 2↑↑7 and with every coefficient below 2↑↑8 in absolute value, such that a rational number q is an
integer if and only if P(q, w) = 0 for some tuple w of 292,890,231,904 rational numbers. Here 2↑↑n is a tower of n
twos (2↑↑1 = 2 and 2↑↑(n+1) = 2^(2↑↑n)). `scripts/check_target.py` confirms that this statement is textually
identical, up to whitespace, to upstream's frozen statement of Theorem 1.1 in `lean/Frozen/BoundedIntegerPolynomial.lean`.

The headline Lean theorem is
`ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzThm35ReadingA_heckeContinuation_functionalEquation5_grossZagier`
(`ZInQKernel/MainLiterature.lean`); its name lists its five hypotheses, and upstream's CI registers each of them as
a target (`KERNEL_CONTRACT.json`). On the fork, `ZInQ.Contrib.functionalEquation5` and
`ZInQ.Contrib.heckeContinuation` prove two of them, with exactly the registered names and types, and
`ZInQ.Contrib.GaussFE.frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagier`
(`ZInQKernel/Contrib/GaussFE/Headline.lean`) proves `ZInQ.FrozenTarget` from the other three.
`ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner`
(`ZInQKernel/Contrib/GZTheta/NewCMFinal.lean`) proves it from H, reading A, `ZInQ.GZDecomp.FHNonvanishing` and
`ZInQ.GZDecomp.GrossZagierHeegner`, and
`ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd`
(`ZInQKernel/Contrib/GZStatements/Weak.lean`) from forms of the last two restricted to the curves C_d. Other
variants, listed in README.md, take other forms of the positive-rank statement, for example `Literature.TYZRow5b`
in place of items 3 and 4.

## The hypotheses

### Positive rank

The construction needs a rational point of infinite order on the congruent number curve C_d: y² = x³ − d²x for
every squarefree d ≡ 5 (mod 8) whose genus sum T5bCl(d) is odd. Here T5bCl(d) ∈ Z/2 is the sum, over the set
partitions of the primes of d with one block ≡ 7, one block ≡ 3 and all other blocks ≡ 1 (mod 8), of the products
over the blocks B of #2Cl(Q(√−d_B)), the order of the subgroup of squares in the class group, where d_B is the
product of the primes in B; T5aCl(d) is the same sum over the partitions with one block ≡ 5 and all others ≡ 1
(mod 8). Lean derives this positive-rank statement from four statements over Mathlib's L-series of an elliptic
curve (`WeierstrassCurve.LSeries`):

1. `Literature.GrossZagier`: if an analytic continuation of L(E, s) has a simple zero at s = 1, then E(Q) has a
   point of infinite order, for every elliptic curve E over Q. This is Gross–Zagier (1986) with an auxiliary
   quadratic twist (Bump–Friedberg–Hoffstein 1990) and modularity (Breuil–Conrad–Diamond–Taylor 2001), not one
   printed sentence. The proof needs it only for C_d with d ≡ 5 (mod 8) squarefree, and on the fork
   `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves` replaces it by three statements:
   that the theta series of the Hecke character of C_d is a newform (Hecke, Shimura), the nonvanishing of
   central twisted values (Friedberg–Hoffstein, Bump–Friedberg–Hoffstein), and Gross–Zagier with Gross's
   conjugation relation, with all the glue proved (docs/research/gz-decomp.md). The first of the three is now
   proved (`ZInQ.GZTheta.heckeThetaNewform`), with Hecke's theorem for y² = x³ − x and the Atkin–Li theorem that
   a quadratic twist of a newform is new at the expected level (`ZInQ.GZTheta.atkinLiTwistNew`) proved too
   (docs/research/gz-theta.md, docs/research/atkin-li.md), so the remaining hypotheses are
   `ZInQ.GZDecomp.FHNonvanishing` and `ZInQ.GZDecomp.GrossZagierHeegner`. A statement review by AI models found
   neither stronger than the published theorem it cites, provided Friedberg–Hoffstein's theorem has the generality
   the review recalls (not yet checked against the paper); Lean also derives the frozen statement from weaker
   forms of the two, restricted to the curves C_d, and proves that the restricted Gross–Zagier statement follows
   from `Literature.GrossZagier` (docs/research/gz-statements.md).
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
the encoding is exactly as strong as item 4. A second route derives item 4 in Lean
(`scratch/cm-bridge/Bridge.lean`, docs/research/cm-bridge.md) from three printed results of Tian, Yuan and Zhang
stated over genuine definitions (docs/research/tyz-decomp.md), three more of their results (their Lemma 3.18 on
torsion, and their Theorems 3.3 and 3.5 and Lemma 3.21(1) for the genus points that the project fixes), and one
textbook theorem, the main theorem of complex multiplication for the values of rational
modular functions on X₀(N) at Heegner points (`Shimura.ShimuraReciprocityModFn`; Shimura 1971, Thm 5.4). The
statements for the fixed genus points have been compared with the paper only by AI models.

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

docs/research/h-decomposition.md breaks H into **leaves**, theorems from the literature that are stated in Lean
and assumed until someone proves them, and **glue**, the arguments that connect them, which the project must
prove in Lean. On the manuscript's route H follows from 23 research-level theorems (Shimura and Deligne on the
level-3 Shimura curve of discriminant 6, Baba–Granath, Lin–Yang, Igusa, González–Rotger, Raynaud, Serre–Tate,
Grothendieck, Faltings 1983 twice (semisimplicity and the Tate conjecture; the Faltings height under isogeny),
de Rham comparison, Berger, Pan's Fontaine–Mazur theorem, Saito or Kato, Deligne, Deligne–Serre, Shimura on
J₁(N), Carayol, Javanpeykar, Gaudron–Rémond, Bost, Pazuki, and the theorem that the stable Faltings height is
finite and attained by Néron models), 35 textbook theorems (among them the existence of Jacobians and of Néron
models, the dimension of J₁(N), the analytic uniformization of abelian varieties, and five facts about elliptic
curves and function fields from which X₁(N) and its Belyi map are built), and 20 glue steps. The project's
assemblies split these steps into smaller named statements and prove them one by one; the canonical assembly, below,
needs one glue statement. Its leaves differ from the manuscript's list: some leaves are split into several
statements, some textbook theorems are proved, and the project's reductions add new ones.

- **The top theorem.** `HDec.HSyn.sixContactMin_of_open4` (`scratch/leaf-fold4/Leaves4.lean`,
  docs/research/leaf-fold4.md) proves `ZInQ.SixContactMin`, the kernel's own statement of H, from 66 named
  hypotheses, none of them a placeholder: 26 research-level leaves (the 23 research-level theorems, some split
  into several statements, with the uniformization clause R1(b) and Carayol's theorem in concrete form), 19
  textbook leaves, 20 leaves that the project's reductions introduced (13 published theorems or consequences of
  them, and 7 candidates), and one glue statement. Section 2 of the note lists all 66, and section 3 groups the 65
  leaves by the theory they come from: Shimura curves with quaternionic multiplication (16), theta functions and
  Siegel modular forms of genus 2 (2), abelian varieties (14), Néron models, reduction and monodromy (6), scheme
  theory (4), Faltings 1983 and Faltings heights (8), p-adic Hodge theory (6), Galois representations of modular
  forms (5), and modular and algebraic curves (4). The glue statement, `HeckeVertWitness`, asks for one unramified
  vertical prime above each prime p > 324 in the Hecke cover; it is equivalent to the project's Lemma NV. A separate reduction (docs/research/vert-witness.md, not folded in) derives it from one leaf,
  good reduction of the curve Y₃, and three smaller glue statements. Compared with the previous assembly, three
  glue statements are proved outright and two more are reduced to leaves; of the leaves, two now follow from other
  leaves, one is no longer needed and one is replaced by its published form, while seven new leaves enter.
- **Statement review.** AI models reviewed the 62 leaves of the previous assembly, most of which are among the
  current 65 (docs/research/leaf-review-a.md, docs/research/leaf-review-b.md): 8 are published statements and 54
  are consequences of published statements, each with its derivation written out; none is stronger than its
  source. No human has reviewed them. The reviews list the assumptions they rest on, among them a lemma fixing the
  principal polarization of a QM abelian surface whose published locators are unverified, a check of the Shimura
  curve's moduli problem that still needs a human, and the definition of the stable Faltings height. Three of the
  new leaves are flagged for a human check (docs/research/leaf-fold4.md, section 3).
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
- **Textbook leaves proved** since 2026-11-12: Skolem–Noether, Brauer–Nesbitt in characteristic 0, Herbrand's
  theorem, Abhyankar's lemma, the local square-root criterion (from local Kronecker–Weber), Kronecker–Weber, local Kronecker–Weber
  (part (a)), Chebotarev's theorem (finite form), the global forms of Hilbert's different formula and of the
  different bound, the existence of a newform with the eigenvalues of a Hecke eigenform, the computation of local
  `H²(G_{ℚ_v}, ℤ/2)` in cochain form, the vanishing of unramified local classes, Brauer–Hasse–Noether with
  reciprocity for `H²(G_ℚ, ℤ/2)`, the structure of the N-torsion of an elliptic curve, good reduction implying
  unramified torsion over k(T), and the Clebsch–Bolza–Igusa separation of binary sextics by their Igusa invariants; the
  freeness of Tate modules (T26) now follows from the torsion leaf T5. Most of these proofs are under
  `ZInQKernel/Contrib/`, and many use the class field theory and modular forms of the Tau Ceti library (Apache-2.0), which is vendored there (its
  license and notice files are in `ThirdParty/TauCeti/`, and the vendored files that were modified carry the change
  notices that Apache-2.0 §4(b) asks for, as a script checks). On a fork branch, Zariski–Nagata purity is proved in
  the form the proof uses (over a regular base of dimension at most 2). The rational cusp of X₁(N) now follows from
  the single leaf `X0Transitive` (X₀(N) is irreducible: the Galois group of ℚ(j) permutes the cyclic subgroups of
  order N of the generic elliptic curve transitively), and Zariski's connectedness theorem replaces an earlier,
  less standard leaf. Further work on the fork's main, not yet folded into the assembly, derives T9 and Serre's
  lemma from other leaves and reduces T3, T6-T8, T11(b), T34, T38 and T41 to smaller statements
  (docs/research/av-b1.md, av-b2.md, curves-g.md, neron-c.md).
- **Proved glue.** Apart from `HeckeVertWitness`, every glue step of the canonical assembly is proved from the
  leaves, with no `sorry`, in the kernel-checked library under `ZInQKernel/HDecomp/` and `ZInQKernel/Contrib/` or
  in the assembly's scratch files. Among them: the step G4 (the Hom field), from
  leaves alone; the adelic bookkeeping of the normalizer of the quaternion order, with |Γ'| = 144, over Mathlib's
  finite adeles; the model of X₁(N) over Q and its Belyi map; the Galois representation of a newform as a
  subrepresentation of the Tate module of J₁(N), its semisimplicity and continuity, and its comparison with two
  other Galois representations; the whole last stretch of the glue (from the level bound, the theta point and the
  height inequalities to H); the manuscript's Brauer and cochain steps; good reduction of the abelian surface away
  from 3; absolute irreducibility and the nonzero homomorphism step; the trace comparison; the conductor bound; the
  core of G10 (the conjugate twist is nontrivial); the count of inner twists and the unramified conjugates; the
  field of the kernel at step G4; the base change of abelian varieties and the multiplication isogeny, from
  Mathlib alone; the appendix lemma (G9), from the amended R10 alone; the comparison of two moduli maps
  (`MobiusGlue`), from one textbook leaf; the Kummer step of Proposition TS; the curve charts of the Hecke covers,
  including their properness and quasi-finiteness; the Galois descent of twists; the base change of the Hodge
  line, of the invariant differentials and of complex points; the uniqueness of the Hauptmodul that the period
  map uses (`hauptmodulUnique`, with a certified numerical evaluation of a theta value); the period map; and the spreading out of an
  abelian variety over a number field, from three statements of EGA IV.
- **Still missing from every Lean library:** the definitions that section 4 of docs/research/h-decomposition.md
  lists. None of them is behind a placeholder any more: conductors of ℓ-adic representations are defined, and the
  complex uniformization of the Shimura curve is stated concretely in family form. Mathlib cannot yet construct a
  nonzero abelian variety; a bridge to the Jacobians of the AxiomMath/Mordell library is on a branch of the fork,
  waiting for a build cache. The stable Faltings height has a Lean definition, and the height leaves are stated
  over it; whether that definition agrees with Faltings' is one of the assumptions the statement review lists.
  Dimension theory (the dimension of an integral variety is the transcendence degree of its function field, and
  the local rings of a smooth variety at its closed points are regular of the expected dimension), and the absolute Frobenius of a scheme of
  characteristic p are now in the library, under `ZInQKernel/Contrib/Dim/` and `ZInQKernel/Contrib/AbsFrob/`.
- **Fallback route.** An alternative modularity route (Khare–Wintenberger with Ribet) needs 20 research-level
  theorems; one adversarial model review, and no human, found it sound subject to five repairs that are not yet
  written, and whether Ribet's 1992 proceedings paper was refereed is unchecked.

## How to help

Claim a subgoal before starting: the tracking issue https://github.com/elliotglazer/diophantine-z-q/issues/37
lists the open-target issues (one per topic), the definitions to build, the leaves, the open glue, and the pull
requests that already prove some of the targets.
Of upstream's five registered targets, two have proofs on the fork (`ZInQ.Contrib.heckeContinuation`,
`ZInQ.Contrib.functionalEquation5`), proposed upstream in pull request #64, and three are open:
`ZInQ.Contrib.sixContactMin` (H), `ZInQ.Contrib.tyzThm35ReadingA` and `ZInQ.Contrib.grossZagier`.
Pull requests go to the main branch of https://github.com/elliotglazer/diophantine-z-q. A merge currently
requires the required CI checks to pass (among them the complete kernel build and exact-target audit, and the
accepted Lean helpers and axiom audit) on a branch that is up to date with main, with every review thread
resolved. The live ruleset (https://github.com/elliotglazer/diophantine-z-q/rules/26781429) shows what a merge
currently requires, and upstream's CONTRIBUTING.md says that review requirements will be stated in
docs/research-review/README.md once the project's new review protocol is implemented; CI alone does not establish
that an argument is correct. The open statements are grouped as upstream issues, one per topic, listed in the
tracking issue; they follow the rows of docs/research/frontier.md, whose live version is on the fork's branch
wip/frontier. Section 2 of docs/research/leaf-fold4.md lists the 66 hypotheses of the canonical assembly of H, and
section 3 groups its leaves by theory. The project's own agents record who is working on what in
https://github.com/Deicyde/diophantine-z-q/issues/3. To build and check: `lake exe cache get`, then
`lake build ZInQKernel`; then `lake env lean scripts/print_axioms.lean` (every declaration listed must depend only on
the three standard axioms) and `python3 scripts/check_target.py`.

## Verification

Every Lean change is built before it reaches main. At the current Lean (fork main 71dc3f1b):
- the library build completes (10,013 jobs), all 542 declarations listed in `scripts/print_axioms.lean` (the
  headline and its variants, the reductions, the Proposition N lemmas, and the glue lemmas of the decomposition
  of H) depend only on the three standard axioms, with no `sorry`, and `scripts/check_target.py` confirms the
  statement;
- all 2,064 files under `ZInQKernel/Contrib/` build (11,973 jobs, no error), most of them the vendored Tau Ceti
  library, and the 138 axiom reports of `scratch/contrib-check/Check.lean`, among them the two proofs of
  hypotheses and the four headline variants above, list only the standard axioms, with no `sorry`;
- `scratch/leaf-fold4/Leaves4.lean` compiles with no error and no `sorry`, and its 326 axiom reports (among them
  `HDec.HSyn.sixContactMin_of_open4`) list only the standard axioms; the earlier
  `scratch/h-decomposition/Leaves.lean` compiles cleanly too;
- the site builds with no problems (163 pages; the blueprint has 735 articles and 2,303 dependencies), and the
  blueprint audit is at its baseline.

An independent machine re-checked an earlier snapshot proposed for pull request #24 (before Proposition N): 9,923
jobs, 80 declarations with standard axioms, and an audit replay of 33,548 declarations with 0 open statements.
GitHub has disabled Actions on the fork since 2026-11-10, so these checks run on the project's own machines; on the
upstream repository, the kernel build with an exact-target audit is among the checks required on every pull request
to main (since #36).

## Where the details are

- README.md: the headline, every hypothesis with its sources and caveats, and the list of variant theorems.
- docs/research/leaf-fold4.md: the canonical assembly of H, with all 66 hypotheses (section 2) and the leaves grouped
  by theory (section 3).
- docs/research/leaf-review-a.md, docs/research/leaf-review-b.md: the statement review of the leaves.
- docs/research/h-decomposition.md: the original decomposition of H into leaves (section 2) and glue steps
  (section 3), the missing definitions (section 4), work packages for contributors (section 5), and risks
  (section 6); its leaf lists and glue counts predate the newer assemblies.
- docs/research/frontier.md: the list of every open statement on the path to `ZInQ.FrozenTarget`.
- docs/research/gz-decomp.md, docs/research/gz-theta.md, docs/research/atkin-li.md, docs/research/gz-statements.md:
  the reduction of Gross–Zagier, the proof of the newform statement, and the review of the two remaining statements.
- docs/research/tyz-decomp.md, docs/research/cm-bridge.md: the reductions of reading A.
- docs/research/h-trust.md: the proof of Theorem 4.1 step by step, with every supplier and its review status.
- docs/research/gauss-proof.md, docs/research/hecke-all.md, docs/research/p-side.md: the Lean proofs of items 2
  and 3 and of the facts about the coefficients of L(C_d, s).
- docs/research/locators.md: the audit of the literature citations against primary sources.
- KERNEL_PLAN.md: how the proof is organized in Lean, and how to build and check it.
- The blueprint site above: every statement with its dependencies and its Lean declaration.

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
