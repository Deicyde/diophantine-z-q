# Z is Diophantine in Q: where the Lean formalization stands (2026-11-12)

Repository: https://github.com/Deicyde/diophantine-z-q, main = 0b62d570. Mirrored upstream as branch deicyde/kernel-formalization of
https://github.com/elliotglazer/diophantine-z-q (pull request #24 carries an earlier snapshot).

## The claim in one paragraph

Glazer's Theorem 1.1, in the exact form frozen upstream, is proved in Lean 4 with Mathlib from a short list of
hypotheses, and the Lean kernel has checked the whole implication: no `sorry`, no `native_decide`, only the
standard axioms `propext`, `Classical.choice`, `Quot.sound`. The statement (`ZInQ.FrozenTarget`) says: there is
one polynomial P with integer coefficients in 292,890,231,905 variables, of total degree below 2↑↑7 and with
coefficients below 2↑↑8 in absolute value, such that a rational q is an integer if and only if
P(q, w) = 0 for some rational w. A script checks that this statement is textually identical (up to whitespace)
to upstream's frozen statement of Theorem 1.1. The hypotheses are Lean propositions passed as assumptions (never
as axioms): four statements about L-functions taken from the literature, and one instance of the manuscript's own
Theorem 4.1. They are listed next.

## What is assumed

Positive rank of the congruent number curves C_d: y² = x³ − d²x for the squarefree d ≡ 5 (mod 8) whose genus
sum T5bCl(d) is odd (the curves the construction needs). Each statement below is a Lean proposition over
Mathlib's own L-series of an elliptic curve.
1. `Literature.GrossZagier`: if an analytic continuation of L(E, s) has a simple zero at s = 1, then E(Q) has a
   point of infinite order (for every elliptic curve E over Q). Gross–Zagier 1986, with an auxiliary twist
   (Bump–Friedberg–Hoffstein 1990) and modularity (Breuil–Conrad–Diamond–Taylor 2001); not one printed sentence.
2. `Literature.FunctionalEquation5`: the functional equation of L(C_d, s), d ≡ 5 (mod 8), with root number −1,
   on the strip 0 < Re s < 2 (Deuring, Hecke; Birch–Stephens 1966); a textbook consequence.
3. Tian–Yuan–Zhang, as two statements: `Literature.TYZThm35ReadingA` (the intended reading of Theorem 3.5(2) of
   arXiv:1411.4728v1, used only in the case 𝓛(n) = 0, a special case of the printed hypothesis) and
   `Literature.HeckeContinuation` (textbook). The Lean theorem `tyzRow5b_of_readingA` turns the pair into the
   form `Literature.TYZRow5b` that the headline theorem takes.

The six-contact height estimate H (`ZInQ.SixContactMin`): the one instance of the manuscript's Theorem 4.1 that
the proof uses. For every rational u outside an explicit exceptional set, the height of u is at most an explicit
constant times the 24th power of the "contact support" of u. H is not a published theorem: it is Theorem 4.1 of
Glazer's manuscript, whose proof combines refereed theorems and exact computations with new arguments (the
manuscript's and the repository's) that only AI models have reviewed (docs/research/h-trust.md).

The headline Lean theorem is
`ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzRow5b_functionalEquation5_grossZagier`
(ZInQKernel/MainLiterature.lean). Composing it with the kernel-checked `tyzRow5b_of_readingA` gives the statement
from H, items 1 and 2, and the two TYZ statements; a single theorem with exactly those hypotheses is being added.

## Caveats on Tian–Yuan–Zhang

Neither TYZ form is a printed statement in any refereed text that we have read. Theorem 1.2 of the arXiv version, read literally, is
false (d = 26565 and 33117 are counterexamples). The proof of Theorem 3.5(2) in the paper passes through a
proposition whose proof is only sketched. An audit of the journal version (Asian J. Math. 21, 2017) by AI agents
with web access found that its Theorem 1.4 is the arXiv Theorem 1.2 with the same restriction, so the same two
values of d are counterexamples there too; no human has checked this.
Supporting evidence, not a hypothesis of the headline: `TYZRow5b` and `TYZThm35ReadingA` are also proved in Lean
from `PropN.TYZInputs`, which encodes consequences of results printed in the arXiv version together with two
standard facts TYZ use without printing (one of them Hecke's continuation); the encoding's faithfulness has been
checked only by AI models. The Lean proof follows a new argument (Proposition N) that AI models reviewed twice and
no human has reviewed.

## What is proved in Lean with no hypotheses

The construction of the polynomial and every finite computation about it (degree, variable count, coefficient
bounds) run in the kernel. Several of the manuscript's inputs are no longer hypotheses:
- the prime-pattern input is replaced by Green–Tao (Ilin's Apache-2.0 Lean proof, vendored and extended to
  dense subsets of the primes) together with a density statement for the good primes, proved with Mathlib's
  Chebyshev bounds and a Selberg sieve vendored from the PrimeNumberTheoremAnd project;
- the Mordell–Weil input and the catalogue bound are theorems;
- the pole statement is proved from positive rank.
On the positive-rank side, Lean proves Rédei's formula, the identification of Mathlib's L-series of C_d with
the classical one, the reduction of the rank statement to the four L-function statements above, and
Proposition N from the encoded inputs `PropN.TYZInputs`.

## The decomposition of H for crowdsourcing (docs/research/h-decomposition.md)

On the manuscript's route, H follows from 22 research-level theorems of the literature (Shimura and Deligne on
the level-3 Shimura curve of discriminant 6, Baba–Granath, Lin–Yang, Igusa, González–Rotger, Raynaud,
Serre–Tate, Grothendieck, Faltings 1983 (twice: semisimplicity and the Tate conjecture; the Faltings height
under isogeny), de Rham comparison, Berger, Pan's Fontaine–Mazur theorem, Saito or Kato,
Deligne, Deligne–Serre, Shimura on J₁(N), Carayol, Javanpeykar, Gaudron–Rémond, Bost, Pazuki), 32 textbook
theorems in six groups, and 20 glue steps (the manuscript's new arguments, the repository's replacement
arguments, bookkeeping). An audit of the citations against the primary sources by AI agents with web access
(docs/research/locators.md, branch wip/locators) corrected several theorem and example numbers; its corrections
are being applied, and some locators (Faltings 1983, Serre–Tate, SGA 7, Bost's constant, Shimura 1967) are still
unverified. Several leaves are derived or assembled forms of the printed theorems, which the note flags for a
check that they are not stronger than published.
- In Lean today: 40 of the 54 leaves are stated over genuine definitions (`scratch/h-decomposition/Leaves.lean`
  compiles, no `axiom`); the other 14 are named placeholders with no content until their definitions exist.
- The top theorem "leaves imply H" is stated in Lean with conclusion `ZInQ.SixContactMin`; its hypotheses are
  the leaves. Its proof has exactly one `sorry` (`HSyn.glueOutputs_of_leaves`, which does not yet use the
  leaves): it stands for most of the glue, from the leaves to a numerical interface that is itself essentially
  a height bound. Only the last steps, from
  that interface to H, are proved on that path.
- Proved in Lean as separate lemmas, each from its leaves (not yet connected to the top theorem): the whole last stretch of the glue (from the level bound, the theta
  point and the height inequalities to H), Glazer's Brauer and cochain steps, step A6 (good reduction away from
  3), parts of steps C2 and E1 (modulo one named algebra statement), the Galois side of
  step C10, the degree bound of step D1 in local form, steps D3 and D4 of the conductor bound, and elementary
  pieces of most other steps.
- Not statable in any Lean library today: the Shimura curve as a moduli scheme with its canonical model, Néron
  models, X₁(N) and J₁(N) over Q, the stable Faltings height, and conductors of ℓ-adic representations; Mathlib
  cannot yet construct a nonzero abelian variety.
- An alternative modularity route (Khare–Wintenberger with Ribet) needs 20 research-level theorems; one
  adversarial model review, and no human, found it sound subject to five repairs that are not yet written, and
  whether Ribet's 1992 proceedings paper was refereed is unchecked; it is kept as the fallback.

So the accurate claim is: the main theorem is proved in Lean from H and a positive-rank statement for the
congruent number curves with T5bCl(d) odd; that statement is reduced in Lean to the four L-function statements
above; H is reduced on paper to the listed literature plus 20
glue steps. It is not yet true that formalizing the literature theorems alone completes the proof: most of the
glue for H (Glazer's descent, modularity and conductor arguments, the repository's replacement lemmas) still has
to be formalized, and it has been reviewed only by AI models.

## Verification

Fork main's Lean was rebuilt after its last change: 9,925 build jobs, all 91 declarations in
`scripts/print_axioms.lean` depend only on the three standard axioms, `scripts/check_target.py` confirms the
statement, and the repository's kernel-trust audit matches its baseline. An independent machine re-checked the
earlier snapshot proposed for pull request #24 (before Proposition N): 9,923 jobs, 80 declarations with standard
axioms, and an audit replay of 33,548 declarations with 0 open statements. GitHub has disabled Actions on the
fork since 2026-11-10, so these checks run on our own machines. The blueprint site
https://deicyde.github.io/diophantine-z-q/ is published again (from a branch) with the current vault; its
main-theorem page is being updated to the form above.
