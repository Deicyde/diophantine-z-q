# hcm-dict results log

Base: wip/leaf-fold33b 4da8d4f32 (origin/main merged: already up to date).
Build tree: reflink copy of the leaf-fold33b worktree's .lake/build and lean/.lake/build (same commit, Main.lean identical).

## Target
`T5Glue.ShimuraMainCM` (ZInQKernel/Contrib/OneProof/RingClassLattice.lean:912), frozenTarget binder `hCM`;
kinds.tsv row 37: consequence / GLUE / GLUE.

## Inputs found (VERIFIED, read in tree)
- Vendored FLT (Apache-2.0) `PeriodPair.isUniformization_toPoint` : `(℘, ℘'/2)` is a surjective group hom
  `ℂ → L.weierstrassCurve(ℂ)` with kernel exactly `L.lattice` (`y² = x³ − g₂/4·x − g₃/4`), built in tree.
- `PeriodPair.discriminant_ne_zero`, `PeriodPair.exists_variableChange_smul_weierstrassCurve_eq` (vendored, built).
- Mathlib `PeriodPair.analyticOnNhd_weierstrassP`, `analyticOnNhd_derivWeierstrassP`, `deriv_weierstrassP`,
  `DiscreteTopology L.lattice`.
- `T5Glue.IsScale` + `.g₂ .g₃ .weierstrassP .derivWeierstrassP` (RingClassLattice.lean §1).
- Local holomorphic lift through `℘` (vendored S_PeriodPair_exists_differentiable..., ModularCurve
  `kw_surgehgf4_hH2d_...`): template for the local lift step.

## Statements (all in ZInQKernel/Contrib/OneProof/ShimuraMainCM.lean, namespace ZInQ.Contrib.HCMDict; dev copy scratch/hcm-dict/Dict.lean)
- `conjPt σ : E(ℂ) → E^σ(ℂ)`, `(x,y) ↦ (σx,σy)`, `O ↦ O`.
- `IsAnalyticUnif E Λ ξ`: ξ : ℂ → E(ℂ) additive, onto, `ξ z = 0 ↔ z ∈ Λ`, holomorphic in affine coordinates
  (open U, DifferentiableOn X Y, ξ = some (X z) (Y z)) at every z₀ with ξ z₀ ≠ 0.
- LEAF `ShimuraThm54` (printed form of Shimura 1971 Thm 5.4; E short Weierstrass, uniqueness dropped).
- `shimuraMainCM_of_printed : ShimuraThm54 → T5Glue.ShimuraMainCM`.
- Dictionary: `isAnalyticUnif_iff L₀ L ξ : IsAnalyticUnif E_{L₀} L ξ ↔ ∃ α, IsScale L₀ L α ∧ ξ = ξ_{L₀}(α ·)`;
  `exists_lattice_eq`: every short elliptic model over ℂ is some `L₀.weierstrassCurve`.

## Compile outcomes (VERIFIED)
- scratch/hcm-dict/Dict.lean: compiles, `shimuraMainCM_of_printed` axioms [propext, Classical.choice, Quot.sound].
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.ShimuraMainCM`:
  success (14195 jobs; Main replayed, new module ~10 s).
- Discharges.lean: `DISCHARGES [hCM] by ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed / still assumes:
  [ZInQ.Contrib.HCMDict.ShimuraThm54] / axioms: [propext, Classical.choice, Quot.sound]` (Discharges-output.txt).
- FoldCheck.lean: `frozenTarget_hCMPrinted` (calls frozenTarget) and `frozenTarget_hCMPrinted'` (folded Main body),
  both standard axioms (FoldCheck-output.txt).
- MainFolded.lean (Main.lean with the fold applied, compiled standalone): `ZInQ.OneProof.frozenTarget` standard axioms.

## Count
- hCM row: consequence/GLUE/GLUE → published (unread)/LEAF/LEAF (kinds-row.tsv). strict GLUE 22 → 21,
  strictest GLUE 22 → 21; no new GLUE (the only new statement is the leaf ShimuraThm54).
