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
- `FibreQMPeriod` (GLUE): the existential form of `FibreQMPeriodAll` (some `σ`, some uniformization).
- `FibreThetaF1` (GLUE, proved from `FibreQMPeriod`).
- `ThetaRatiosAlgebraic` (LEAF candidate): some `θ_{m₀}(Ω) ≠ 0` and all `θ_m/θ_{m₀}` algebraic;
  implies `ThetaNullAlgebraic` (proved, `thetaNullAlgebraic_of_ratios`, `L = ℚ(ratios) ⊆ ℂ`).

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

- run5 (02:11-02:14): 0 errors, no `sorry`, 2m52s; adds `FibreQMPeriod`, `fibreQMPeriod_of_all`,
  `fibreThetaF1_of_qm`, `thetaPointOfFibre_of_qm : FibreQMPeriod → ThetaNullAlgebraic →
  ThetaPointOfFibre`; all axioms `[propext, Classical.choice, Quot.sound]`.
- run6: 3 errors (`ι` is a notation token in this file; binder renamed `Idx`); run7 clean.
- run8 (02:23-02:26): 0 errors, no `sorry`, 2m40s. Adds `exists_nf_of_isAlgebraic`,
  `thetaNullAlgebraic_of_ratios`, `thetaPointOfFibre_of_qm_ratios : FibreQMPeriod →
  ThetaRatiosAlgebraic → ThetaPointOfFibre`; `glueOutputs_of_leaves_thetaParts` now takes
  `FibreQMPeriod`, `ThetaRatiosAlgebraic` in place of `ThetaPointOfFibre`. All axioms
  `[propext, Classical.choice, Quot.sound]`.

## Findings
- The piece is not false or vacuous (model argument, docs/research/g0-thetapoint.md §3). Its
  height clause needs no theta-function input: `z'` is not tied to `z`, and dropping coordinates
  never raises Mathlib's height (VERIFIED, `height_even`).
- `Jmap` in the piece is `ZInQ.JHeight.Jmap` (`-57600F(u)²/G(u)⁶`), VERIFIED by reading.

## Numerical checks (`theta_check.py`, output `theta_check_out.txt`; mpmath 220/430 digits, PARI algdep)
- CM point `τ₋₂₄ = 4.18154…i` (fixed point of `ι(μ)`): `j_θ(Ω(τ)) = -16/27` to 220 digits; the six odd
  theta constants are `< 1e-220`; min even `|θ_m| = 0.785`. Every `(θ_m/θ_{m₀})⁴` satisfies an integer
  polynomial of degree 2 or 4 with coefficients `< 10³`, with residual `< 1e-150`. (VERIFIED
  numerically. A random number would need coefficients around `10⁵⁰` for such a residual.)
- Non-CM fibre `u = 1`, `J(1) = -14533295809536000000/3556808369970021551449`: `τ_u =
  1.3932949171603… + 0.8693197409124…i` solves `j_θ(Ω(τ)) = J(1)` (residual `3e-42`; found by
  `findroot` near `τ₋₄ = √2 + i`). There the odd theta constants are `< 1e-220`, and min even
  `|θ_m| = 0.185`, so no even theta constant vanishes, consistent with a simple surface.
  Algebraicity is INCONCLUSIVE: degree-12 relations found at 220 digits were spurious, because at
  430 digits the coefficients jump from `10²⁹` to `10⁵⁵`. No relation of degree `≤ 12` and small
  height exists, and the expected degree is unknown.
