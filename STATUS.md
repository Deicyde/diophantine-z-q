# Z is Diophantine in Q: status of the Lean formalization (2026-11-12)

The manuscript *Z is Diophantine in Q* (November 5, 2026; `diophantine_zq.pdf` in
https://github.com/elliotglazer/diophantine-z-q) constructs one polynomial P with integer coefficients such that a rational number q is an integer exactly when
P(q, w) = 0 for some tuple w of rational numbers. This project checks that proof in the Lean 4 proof assistant,
with the Mathlib library.

- Repository: https://github.com/Deicyde/diophantine-z-q (Lean state of fork main 533aa66c)
- Blueprint, with every statement, its dependencies and its Lean declaration: https://deicyde.github.io/diophantine-z-q/

## Status in three lines

- **Proved in Lean, with no gaps:** the manuscript's Theorem 1.1, in exactly the form frozen upstream, follows
  from two inputs: H, a height bound (the manuscript's Theorem 4.1), and a positive-rank statement for certain
  congruent number curves.
- **Reduced in Lean:** the positive-rank statement follows from four statements about L-functions. Three are
  published theorems or textbook consequences of them; the fourth is one reading of a theorem of Tian, Yuan and
  Zhang that no refereed text we found states explicitly (caveats below).
- **Open, and most of the remaining work:** H. On paper it follows from 22 research-level theorems, 32 textbook
  theorems and 20 glue steps (the manuscript's new arguments and this project's replacements). Most of the glue
  is not yet in Lean, and it has been reviewed only by AI models, not by a human.

So formalizing the literature theorems alone would not yet complete the proof.

## How far to trust each part

| Part | Status |
| --- | --- |
| The construction of P and every finite computation about it (variables, degree, coefficients) | proved in Lean, no hypotheses |
| Theorem 1.1 from H and the positive-rank statement | proved in Lean |
| The positive-rank statement from items 1 to 4 below | proved in Lean |
| Items 1 to 3: Gross–Zagier, the functional equation, Hecke's continuation | published theorems or textbook consequences; assumed |
| Item 4: Tian–Yuan–Zhang, reading A | not printed in this form in any refereed text we found; assumed |
| H, the manuscript's Theorem 4.1 (one instance) | unrefereed; its new arguments reviewed only by AI models; assumed |

"Proved in Lean" means the Lean kernel checked it, with no `sorry` (unproved step), no `native_decide` (trusted
external evaluation), and only the standard axioms `propext`, `Classical.choice`, `Quot.sound`. "Assumed" means
stated in Lean as a proposition and passed as a hypothesis, never as an axiom. Everything except these five
hypotheses is machine-checked, so a reader needs to trust only the five statements, not the rest of the
manuscript's argument.

## The statement checked

`ZInQ.FrozenTarget` says: there is a polynomial P with integer coefficients in 292,890,231,905 variables, of total
degree below 2↑↑7 and with every coefficient below 2↑↑8 in absolute value, such that a rational number q is an
integer if and only if P(q, w) = 0 for some tuple w of 292,890,231,904 rational numbers. Here 2↑↑n is a tower of n
twos (2↑↑1 = 2 and 2↑↑(n+1) = 2^(2↑↑n)). `scripts/check_target.py` confirms that this statement is textually
identical, up to whitespace, to upstream's frozen statement of Theorem 1.1 in `lean/Frozen/BoundedIntegerPolynomial.lean`.

The headline Lean theorem is
`ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzThm35ReadingA_heckeContinuation_functionalEquation5_grossZagier`
(`ZInQKernel/MainLiterature.lean`); its name lists its five hypotheses. Other variants, listed in README.md, take
other forms of the positive-rank statement, for example `Literature.TYZRow5b` in place of items 3 and 4.

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
   printed sentence.
2. `Literature.FunctionalEquation5`: for squarefree d ≡ 5 (mod 8), the functional equation of L(C_d, s) with
   conductor 32d² and root number −1 (Deuring, Hecke; Birch–Stephens 1966), stated on the strip 0 < Re s < 2,
   which avoids the points where Mathlib's Gamma function takes the conventional value 0; a textbook consequence.
3. `Literature.HeckeContinuation`: for every positive integer d, L(C_d, s), defined by its Euler product for
   Re s > 3/2, extends to an entire function (Deuring, Hecke: C_d has complex multiplication by Z[i]); standard.
4. `Literature.TYZThm35ReadingA`: for squarefree d ≡ 5 (mod 8), if L(C_d, s) vanishes to order at least 2 at
   s = 1, then T5aCl(d) and T5bCl(d) are both even. This is Theorem 3.5(2) of Tian–Yuan–Zhang (arXiv:1411.4728v1;
   Asian J. Math. 21 (2017)) for n = d, in one reading of its genus sums ("reading A": the decompositions of n are
   set partitions of its primes, each counted once, with a trivial factor allowed), and it is needed only when
   their invariant 𝓛(n) is 0, which happens exactly when the order of vanishing at s = 1 is at least 2. That case
   is a special case of the printed hypothesis.

How they combine: the functional equation with root number −1 makes L(C_d, s) vanish at s = 1; when T5bCl(d) is
odd, items 3 and 4 bound the order of vanishing by 1 (this is the statement `Literature.TYZRow5b`, which the Lean
theorem `Literature.tyzRow5b_of_readingA` proves from them); so the zero is simple, and item 1 gives a point of
infinite order.

**Caveats on item 4.** No refereed text found by the project's literature search (carried out by AI agents)
states reading A explicitly; the one statement found (Smith, arXiv:1603.08479, Theorem 2.1) is unrefereed. TYZ's
introductory theorem with the same parity criteria (Theorem 1.2 of the arXiv version, Theorem 1.4 of the journal
version) requires every factor to exceed 1, and read that way it is false in both versions: d = 26565 and
d = 33117 are counterexamples (exact class-group computations and explicit points of rank at least 3, not checked
in Lean). Read the same way, Theorem 3.5(2) is false too; reading A, which the project uses, is consistent with
both values and with all 32 cases in a scan of squarefree n ≡ 5 (mod 8) below 52000 of analytic rank 3
(docs/research/nt-tyz.md, section 1.4). The paper's proof of
Theorem 3.5(2) passes through its Proposition 3.4, whose proof is only a sketch in the arXiv version; the journal's
proof was not assessed on this point. The comparison of the two versions was made by AI agents with web access;
no human has checked it.

**Supporting evidence, not a hypothesis of the headline.** `TYZRow5b` and `TYZThm35ReadingA` are also proved in
Lean from `PropN.TYZInputs`, which encodes consequences of results printed in the arXiv version together with two
standard facts TYZ use without printing (one of them Hecke's continuation); the encoding's faithfulness has been
checked only by AI models. The Lean proof follows a new argument, Proposition N (docs/research/nt-tyz.md,
section 4), that AI models reviewed twice and no human has reviewed.

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
inputs `PropN.TYZInputs`.

## What is left: the decomposition of H

docs/research/h-decomposition.md breaks H into **leaves**, theorems from the literature that are stated in Lean
and assumed until someone proves them, and **glue**, the arguments that connect them, which the project must
prove in Lean. On the manuscript's route H follows from 22 research-level theorems (Shimura and Deligne on the
level-3 Shimura curve of discriminant 6, Baba–Granath, Lin–Yang, Igusa, González–Rotger, Raynaud, Serre–Tate,
Grothendieck, Faltings 1983 twice (semisimplicity and the Tate conjecture; the Faltings height under isogeny),
de Rham comparison, Berger, Pan's Fontaine–Mazur theorem, Saito or Kato, Deligne, Deligne–Serre, Shimura on
J₁(N), Carayol, Javanpeykar, Gaudron–Rémond, Bost, Pazuki), 32 textbook theorems in six groups, and 20 glue steps.

- **Citations.** An audit of the citations against the primary sources by AI agents with web access
  (docs/research/locators.md) corrected several theorem and example numbers, and the corrections are applied.
  Some locators (Faltings 1983, Serre–Tate, SGA 7, Bost's constant, Shimura 1967) are still unverified. Several
  leaves are derived or assembled forms of the printed theorems, which the note flags for a check that they are
  not stronger than published.
- **Repairs.** Reviews on 2026-11-12 found three leaves misstated, and all three are repaired on main: the
  González–Rotger count of CM points now carries the factor 2^b(R) (the step that uses it holds with the correct
  count); the Lean statement of Yu's QM dichotomy (a textbook leaf) now includes Yu's hypothesis that the
  quaternion algebra is indefinite (as first written it was stronger than published); and the branching data of
  the Atkin–Lehner quotient is reworded.
- **Stated in Lean.** 40 of the 54 leaves are stated over genuine definitions in
  `scratch/h-decomposition/Leaves.lean` (it compiles with `lake env lean`, no `axiom`); the other 14 are named
  placeholders with no content until their definitions exist.
- **The top theorem.** "Leaves imply H" is stated in Lean, with the leaves as hypotheses and `ZInQ.SixContactMin`
  as conclusion. Its proof has exactly one `sorry` (`HSyn.glueOutputs_of_leaves`, which does not yet use the
  leaves): it stands for most of the glue, from the leaves to a numerical interface that is itself essentially a
  height bound. Only the last steps, from that interface to H, are proved on that path.
- **Proved glue, as separate lemmas** (each from its leaves; adopted into the kernel-checked library under
  `ZInQKernel/HDecomp/`, no `sorry`; not yet connected to the top theorem): the whole last stretch of the glue
  (from the level bound, the theta point and the height inequalities to H), the manuscript's Brauer and cochain steps,
  good reduction of the abelian surface away from 3, parts of absolute irreducibility and of the nonzero
  homomorphism step (modulo one named algebra statement, `SemisimpleBaseChange`), the Galois side of the trace
  comparison, the degree bound of the conductor estimate in local form, two further steps of the conductor bound,
  and elementary pieces of most other steps.
- **Not statable in any Lean library today:** the Shimura curve as a moduli scheme with its canonical model,
  Néron models, X₁(N) and J₁(N) over Q, the stable Faltings height, and conductors of ℓ-adic representations.
  Mathlib cannot yet construct a nonzero abelian variety. Drafts on main (under `scratch/`, not yet in the counts
  above) now give a Lean definition of the stable Faltings height, whose non-vacuity checks are still open, and
  concrete statements for several placeholder leaves (the Shimura-curve leaves and Eichler–Shimura in J₁(N)).
- **Fallback route.** An alternative modularity route (Khare–Wintenberger with Ribet) needs 20 research-level
  theorems; one adversarial model review, and no human, found it sound subject to five repairs that are not yet
  written, and whether Ribet's 1992 proceedings paper was refereed is unchecked.

## How to help

Claim a subgoal in the tracking issue https://github.com/elliotglazer/diophantine-z-q/issues/37 before
starting; it lists targets that can be started now, the definitions to build, the leaves, and the open glue.
Pull requests go to the main branch of https://github.com/elliotglazer/diophantine-z-q. The work packages, with
their dependencies, are also in section 5 of docs/research/h-decomposition.md. To build and check: `lake exe cache get`, then `lake build ZInQKernel`; then
`lake env lean scripts/print_axioms.lean` (every declaration listed must depend only on the three standard axioms)
and `python3 scripts/check_target.py`.

## Verification

Every Lean change is built before it reaches main. At the current Lean (fork main 533aa66c) the build completes;
all 272 declarations listed in `scripts/print_axioms.lean` (the headline and its variants, the
reductions, the Proposition N lemmas, and the glue lemmas of the decomposition of H) depend only on the three
standard axioms, with no `sorry`; `scripts/check_target.py` confirms the statement; and the blueprint checks pass
(657 articles, 2,041 dependencies). An independent machine re-checked an earlier snapshot proposed for pull request
#24 (before Proposition N): 9,923 jobs, 80 declarations with standard axioms, and an audit replay of 33,548
declarations with 0 open statements. GitHub has disabled Actions on the fork since 2026-11-10, so these checks run
on the project's own machines.

## Where the details are

- README.md: the headline, every hypothesis with its sources and caveats, and the list of variant theorems.
- docs/research/h-decomposition.md: the leaves of H (section 2), the glue steps with their Lean status (section 3),
  the missing definitions (section 4), work packages for contributors (section 5), and risks (section 6).
- docs/research/h-trust.md: the proof of Theorem 4.1 step by step, with every supplier and its review status.
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
- **Placeholder:** a leaf that cannot yet be stated because its definitions are missing; it carries no content.
- **Glue:** an argument connecting leaves, which the project must prove in Lean.
