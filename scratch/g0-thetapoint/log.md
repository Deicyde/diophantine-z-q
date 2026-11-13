# g0-thetapoint log

Piece: `HSyn.G0Split.ThetaPointOfFibre` (g0-split missing piece 9; G19, F1 on `A`), unchanged.

## Files
- `ThetaPoint.lean` = `scratch/g0-split/Split.lean` verbatim + one line
  `import ZInQKernel.HDecomp.Analytic.QMLattice` + `part_theta.lean` (assembled by `build.sh`).
- `part_theta.lean`: new section, namespace `HSyn.G0Split.ThetaPt`.
- `Dev.lean`: development copy (local definitions, Mathlib + QMLattice only).
- Prerequisites: `lake build ZInQKernel.HDecomp.Analytic.QMLattice` and
  `lake build ZInQKernel.Hypotheses.JHeight` (builds upstream `lean/` helpers).

## Statements (all in `HSyn.G0Split.ThetaPt`)
- `UniformizationExistsNF` (TEXTBOOK leaf candidate): abelian surface over a number field has an
  analytic uniformization `ℂ² → A(ℂ)_σ` at some `σ`.
- `FibreQMPeriodAll` (GLUE): for the fibre over `J(u)`, every uniformization lattice is linearly
  isomorphic to bp-analytic's `qmLattice τ` for some `τ ∈ ℍ` with `jNum/jDen(Ω(τ)) = J(u)`.
- `ThetaNullAlgebraic` (LEAF-COMPOSITE): for any period matrix `Ω ∈ 𝔥₂` of a uniformization
  lattice, `θ_m(0,Ω) = c⁻¹·emb(z_m)` for a point `z` of a number field.
- `FibreThetaF1` (GLUE, proved from `DimBaseChange` + the first two).

## Results (VERIFIED: compiled)
- run4 (02:07-02:10): `lake env lean scratch/g0-thetapoint/ThetaPoint.lean`: 0 errors, no
  `sorry`, 3m04s. `#print axioms` = `[propext, Classical.choice, Quot.sound]` for
  `thetaConst_odd`, `thetaPointOfFibre_of`, `fibreThetaF1_of`, `thetaPointOfFibre_of_parts`,
  `HSyn.glueOutputs_of_leaves_thetaParts`.
- `thetaPointOfFibre_of : FibreThetaF1 → ThetaNullAlgebraic → ThetaPointOfFibre`.
- `fibreThetaF1_of : DimBaseChange → UniformizationExistsNF → FibreQMPeriodAll → FibreThetaF1`.
- `thetaPointOfFibre_of_parts`: the composition.
- `glueOutputs_of_leaves_thetaParts`: g0-split's main theorem with piece 9 replaced by the parts.
- Proved glue lemmas: `f1_of_theta` (degree-0 homogeneity, emb injective), `height_even`
  (Mathlib `Height.logHeight_comp_le`), `jTheta_eq` (= pkg-I1 `jNum/jDen`), `thetaConst_eq_pkgI1`,
  `omega_eq` (`PkgI1.Omega = BPAnalytic.QM.Omega`, `rfl`), `isPeriodMatrix_of_map`,
  `isPeriodMatrix_of_comap`, `isPeriodMatrix_qmLattice`, `isSiegel_Omega`, `thetaConst_odd`
  (odd theta constants vanish, reindexing `n ↦ -n-a`, no summability needed).
- Runs 1-3: run1 failed (upstream `ZInQ` oleans missing, fixed by building JHeight); run2 one error
  (`Matrix.dotProduct_smul` → `dotProduct_smul`); run3 clean.

## Findings
- The piece is not false or vacuous (model argument, docs/research/g0-thetapoint.md §3). Its
  height clause needs no theta-function input: `z'` is not tied to `z`, and dropping coordinates
  never raises Mathlib's height (VERIFIED, `height_even`).
- `Jmap` in the piece is `ZInQ.JHeight.Jmap` (`-57600F(u)²/G(u)⁶`), VERIFIED by reading.
