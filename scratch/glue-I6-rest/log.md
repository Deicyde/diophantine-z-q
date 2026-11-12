# glue-I6-rest results log

## I6Base.lean (pkg-I6's I6.lean copied, plus glue)
- Copied scratch/pkg-I6/I6.lean. `artinConductor_le_of_upper` (sorry in pkg-I6) turned into an
  open statement `def ArtinConductorLeOfUpper : Prop` (no sorry in the file).
- `exists_sq_eq_one_add` adopted verbatim from scratch/glue-conductor/Dyadic.lean.
- PROVED `sq_principalUnits` (D3) from it with s = r − e.
- PROVED `finrank_splittingField_le_factorial`: f separable ⇒ [SplittingField f : K] ≤ (deg f)!
  (Gal f ↪ Perm(rootSet), #rootSet ≤ deg f).
- PROVED `finrank_isSplittingField_le_factorial` (any splitting field).
- PROVED `ramificationIdx_le_finrank_of_numberField`: P.ramificationIdx ℤ ≤ [L:ℚ]
  (Mathlib `sum_ramification_inertia_eq_finrank`, `inertiaDeg_pos`; P = ⊥ case separately).
- PROVED `ramificationIdx_le_factorial`: L splitting field over ℚ of separable f ⇒
  e(P) ≤ (deg f)!, the hypothesis `hea` of glue-conductor's `D1_genuine`.
- Compile 22:28: `lake env lean scratch/glue-I6-rest/I6Base.lean`, no errors; all #print axioms
  [propext, Classical.choice, Quot.sound] (VERIFIED).
