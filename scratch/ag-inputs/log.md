# ag-inputs results log

Task: adversarial review of pi0-x6's `r1pi0Props_of_X6Props` (Galois-component argument for
`π₀(X₆) = 1`), then prove as much of `AGInputs` (over0, overInf, descend) as Mathlib v4.35 allows
and state the rest as leaves.

## Lean

- L1 (VERIFIED, compiled 01:30 PST, `lake env lean scratch/ag-inputs/T1.lean`, no errors, no
  warnings; Mathlib only): `descend_of_leaf : ConnectedGeomConnected → IsProper X.hom →
  ConnectedSpace (X ×_ℚ Spec ℚ̄) → GeometricallyConnected X.hom`.
- L2 (VERIFIED, compiled 01:40 PST, `lake env lean scratch/ag-inputs/AGInputs.lean`, exit 0, no
  errors, no warnings; 15 `#print axioms` lines all `[propext, Classical.choice, Quot.sound]`,
  output in `compile_out.txt`; no `sorry`, no `axiom`). `AGInputs.lean` = pi0-x6's `Pi0X6.lean`
  (namespace renamed `AGIn`) plus §8-§9:
  - `ConnectedGeomConnected` (leaf AG-GC), `spec_rat_ext`, `descend_of_leaf` (proved);
  - `CurveComponentDichotomy` (leaf AG-CD), `meets_fibre_of_finite` (proved);
  - `qmIsoOfConj` (inner twists are isomorphic, proved), `AutModInnFinite` (leaf AutO),
    `twistClasses_finite`, `fibres_finite` (finite `π₆`-fibres from `R2X6Props` + AutO, proved);
  - `agInputs_of_leaves : ConnectedGeomConnected → CurveComponentDichotomy → AutModInnFinite →
    IsProper → SmoothOfRelativeDimension 1 → R2X6Props → AGInputs π₆` (proved; all three fields);
  - `r1pi0Props_of_leaves : X6Props → R2X6Props → R5ptProps → R5fpCount → R2X6CMExact →
    ConnectedGeomConnected → CurveComponentDichotomy → AutModInnFinite →
    GeometricallyConnected X.hom` (proved).
