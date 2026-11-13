# g10-odd results log

## Statements
- `G10Glue` copied verbatim (scratch/g0-mod-galois/part_galois.lean L223-242) into
  scratch/g10-odd/G10Odd.lean §1, with `HSyn.T11_RiemannGAGA`, `HSyn.T12_ArtinComparison`
  (opaque, verbatim from scratch/g0-split/Split.lean L19261-19268), `resQ`, `Vb`, `tate`,
  `Intertwines`, `G10Out` (verbatim). `PkgI3.*`, `PkgI4.*`, `GlueI3.repBaseChange` imported from
  ZInQKernel/HDecomp (bodies identical to Split.lean's copies; diffed: only docstring line breaks
  and extra defs differ). VERIFIED (diff).

## Findings
- F1 (VERIFIED, by reading): `HSyn.T11_RiemannGAGA`, `HSyn.T12_ArtinComparison` are `opaque … : Prop`:
  no content can be extracted from them; any proof of `G10Glue` must not use them.
- F2 (VERIFIED, compiled): `G10Glue` follows from `ConjTwistNontrivial` (new named glue, stated over
  `PkgI3.AbVar.galRep`, `resQ`, `PkgI4.IsComplexConj`), with `PkgI3.FaltingsTate` as its only
  hypothesis. Theorem `G0Galois.g10Glue_of_conjTwist`.
- F3 (VERIFIED, compiled): algebra: `det_eq_neg_one_of_sq_eq_one`, `isComplexConj_mul_self`,
  `isOdd_of_not_pm_one`, `baseChange_injective'`, `galRep_eq_of_central`.

## Compile outcomes
- 2026-11-13 04:18 `lake env lean scratch/g10-odd/G10Odd.lean`: no errors, no warnings (after
  `lake build ZInQKernel.HDecomp.LeafPush2.T ZInQKernel.HDecomp.I3Linalg.C2`).
- 2026-11-13 04:24 §4-§5 added (T12K split, totally real case, corrected statement): compiles,
  no errors. New: `T12K_ComplexConjEigen` (glue target), `ConjTwistOutside` (glue),
  `not_pm_one_of_mem_range`, `g10Glue_of_T12K_conjTwistOutside`, `isOdd_of_T12K_of_forall_mem`,
  `G10GlueConcrete`, `ConjTwistFromLeaves`, `g10GlueConcrete_of_conjTwistFromLeaves`,
  `g10Out_of_conjTwist` (the conclusion without the opaque hypotheses). VERIFIED (compiled).
- 2026-11-13 04:28 §6 added (linear-algebra skeleton: `baseChange_injective₂`,
  `mem_of_one_tmul_mem_span`, `eq_zero_of_holo_of_antiholo`, `betti_skeleton`): compiles.
  `#print axioms` for `g10Glue_of_conjTwist`, `g10Glue_of_T12K_conjTwistOutside`,
  `isOdd_of_T12K_of_forall_mem`, `g10GlueConcrete_of_conjTwistFromLeaves`, `betti_skeleton`:
  [propext, Classical.choice, Quot.sound]. VERIFIED (compiled).
- 2026-11-13 04:31 `ConjTwistFromLeaves`, `G10GlueConcrete` now also take T5
  (`PkgI2.TorsionStructure.{0}`) and T26 (`PkgI3.TateModuleFree`); §7 `t12_of_t12K`
  (`T12K_ComplexConjEigen → ZInQ.LeafPush2.T12_ComplexConjEigen`) added. Compiles; only
  warnings are the `letI` style lints inside the verbatim copy of `resQ_spec`. All six
  `#print axioms`: [propext, Classical.choice, Quot.sound]. VERIFIED (compiled).
- F4 (argument, not machine-checked): `T12_ComplexConjEigen` (over `ℚ`) cannot replace the
  Faltings step when `c ∉ G_K`: for `W = Res_{K/ℚ} A`, `V_ℓ(W) ⊗ ℚ̄_ℓ ≅ (r ⊗ ℚ̄_ℓ[Gal(K/ℚ)])²`, and
  if `c|_K ≠ id` the permutation trace of `c` is `0`, so the eigenspace dimensions of `c` on
  `V_ℓ(W)` are `(2n, 2n)` whether or not `r(c) = ±1`.
- F5 (STANDARD argument; reference Shimura 1975 UNVERIFIED): under G10Glue's hypotheses
  (`End⁰_K(A)` a quaternion division algebra `B`), `K` has no real place: for `c ∈ G_K`, `F_∞`
  commutes with `B` on `H₁(A(ℂ),ℚ)` (free of rank 1 over `B`), so `F_∞ ∈ B^op`, `F_∞² = 1`, hence
  `F_∞ = ±1` (division), contradicting eigenspaces `(2,2)`. So in the application every complex
  conjugation is outside `G_K`, and `ConjTwistOutside` carries all of G10's content.
