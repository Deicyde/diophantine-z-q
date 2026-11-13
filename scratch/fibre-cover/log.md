# fibre-cover results log

## Setup (04:10)
- Base 2dd83306. Built `ZInQKernel.HDecomp.QM.Leaves` (+ Descent.Constants, B2Glue, Mult Constants): 4 min.
- `scratch/fibre-cover/FibreCover.lean`: `IF`, `T`, `IsModelOver`, `FibreCtx`, `RationalFibre`,
  `FibreCoverOut`, `FibreCoverExists` copied verbatim from `scratch/g0-mod-field/ModField.lean`
  (namespace `G0ModField`). Imports: QM.Leaves, Descent.Constants, Descent.B2Glue,
  Multiplication.Certificate.Constants, Hypotheses.JHeight. `lake env lean` ~2 min.
- Pitfall: `open GlueDescent.B3Q` (namespace absent under these imports) makes the whole `open`
  fail; `ι` is a token here (like `η` under `open MonObj`), rename binders.

## run1-3 (04:35): Part 1, FibreCoverOut depends only on the residue field of y
- Proved: `spec_to_specQ_eq` (copied from rv-g0pieces), `exists_factor_of_residueImage_le`
  (`residueImage y ≤ K` ⇒ `y = yK ∘ Spec(K ⊆ ℚ̄)`), `residueImage_le_aux`, `residueImage_comp_le`,
  `isModelOver_of_baseChange` (IsBaseChangeOf + QML3.Iso ⇒ IsModelOver, via
  `IsPullback.isoPullback`), `rationalFibre_of_le` (R1fp ⇒ rational fibre over any `K ⊇ residueImage y`),
  `FibreFieldOut` (def), `fibreCoverOut_iff` (R1fp: FibreCoverOut Y Φ u P ↔ FibreFieldOut (residueImage y) u),
  `fibreCoverOut_indep` (two moduli bijections Φ, Φ' with R1fp on the same Y, same point y: G2 agrees).
- VERIFIED: `lake env lean scratch/fibre-cover/FibreCover.lean`: 0 errors, 0 warnings.
