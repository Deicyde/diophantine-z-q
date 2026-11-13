# g9-derham (fleet note)

**Main result.** g0-mod-galois's `G9Glue` (N5's de Rham descent lemma, glue step G9) is restated
verbatim (`ZInQKernel/Contrib/G9/Statement.lean`). It is reduced, with the standard axioms only, to
two named statements:
`ZInQ.Contrib.G9.g9Glue_of_abVarBaseChange : G9Bridge.AbVarBaseChange → G9Bridge.R10Weights → G0Galois.G9Glue`
(`LocalModel.lean`). `G9Glue` itself is not proved outright.

**Why two hypotheses remain** (docs/research/g9-derham.md §2):
- F1: `G9Out` needs Hodge–Tate multiplicity 0 at every weight other than 0 and −1. R10's Lean form
  (`DeRhamComparison`) gives only the weights 0 and −1. The missing clause is `R10Weights`. It is
  part of the published Hodge–Tate decomposition; recommendation: amend R10.
- F2: R10 lives over local fields, `A` over a number field. `AbVarBaseChange` is base change of
  abelian varieties with `dim` and `V_ℓ` (finiteness of `A[ℓⁿ]`). STANDARD, not in Mathlib.
- F3 (`ℚ̄_p ⊆ B_dR`) is closed: `iotaDR`, by the task's second run (3c).

The route check (first step) passed: G9 is on route P (h-decomposition §1 L467); route K is the
fallback.

**What compiles** (all VERIFIED; `scratch/g9-derham/Axioms.lean`: 22 theorems, each with
`[propext, Classical.choice, Quot.sound]`; no `sorry`): 20 new files in `ZInQKernel/Contrib/G9/`.
`lake build` of `.Partial`, `.LocalModel` and `.G9Weights` succeeds, and these three import all 20.
Exact declarations proved, in namespace `ZInQ.Contrib.G9`:
- `g9Glue_of_abVarBaseChange`, `localModel_of_abVarBaseChange`, `g9Glue_of_localModel`,
  `g9Glue_of_fieldEmb`, `g9Glue_of_bridges`, `fieldEmbBdR`.
- `g9_partial`: without `R10Weights`, `LocalIsDeRham` plus multiplicities 1 at 0 and at −1.
- `coef_descent`: finite coefficient field, no Baire.
- `core_ht`, `core_dR_F`, `core_dR`, `core_htMult`, `overF_count_gen`, `core_count_F`: counting and
  the descent from `F` to `ℚ_ℓ`.
- `PkgI4.bdrAct_mul`, `bdrAct_one`, `htAct`, `drAct`, `descent_finrank`, `speiser_finrank`,
  `range_gfToGqp`.
- By 3c: `iotaDR`, `bdrAct_iotaDR`, `g9_deRham`, `g9_hasHTWeights`, `g9_local`.

T23 and T10 are not used.

**What remains.** Proving `AbVarBaseChange` (algebraic geometry of abelian varieties), and
`R10Weights` (Tate–Sen), or amending R10 to include it.

Deliverables: the Lean files above, docs/research/g9-derham.md, scratch/g9-derham/log.md.
