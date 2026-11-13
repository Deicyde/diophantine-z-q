# product-unif results log

## Run 1 (2026-11-13, from 05:51 PST)

- `lake build ZInQKernel.HDecomp.Faltings.Height`: success, 9051 jobs (VERIFIED).
- `Analysis.lean` (Mathlib only): `rcore`, `ccore`, `exists_isolated`, `exists_countable_add`,
  `rcore_sup_eq_top` (closed subgroups with `H₁ + H₂ = E` have `rcore H₁ ⊔ rcore H₂ = ⊤`; via
  `Measure.addHaar_submodule`), `isClosed_of_local` (subgroup cut out near 0 by functions continuous
  there is closed), `rcore_le_ccore` (identity theorem: real core of a subgroup cut out near 0 by
  holomorphic functions is complex), `eq_zero_of_mem_rcore_discrete`. Compile: 3 iterations
  (squeeze `simpa`, `TopologicalSpace.separableSpace_iff_countable`, `Function.comp_def`); final
  0 errors, 4/4 `#print axioms` standard (VERIFIED).
- `ProductUnif.lean` (imports `ZInQKernel.HDecomp.Faltings.Height` + Mathlib): §0 verbatim copy of
  `scratch/product-height/ProductHeight.lean` lines 404-469 (`ptsProj` … `prodUnif_clauses`),
  800-862 (`dom_comp` … `proj_analyticClauses`), 864-922 (`ProductUnifSplits`,
  `ProductMetrizationOfProductUnif`), in namespace `ZInQ.ProductHeight` (same full names);
  §1 = `Analysis.lean`; §2 `pts_eq_of_evalAt` (two `τ`-points in an affine open with equal
  `evalAt` on `Γ(V)` are equal; via `IsAffineOpen.SpecMap_appLE_fromSpec`,
  `IsAffineOpen.fromSpec_top`), `top_le_preimage_of_mem`, `kerSub_facts` (kernel of a holomorphic
  homomorphism `ℂ^g → 𝒢(ℂ)_τ` is closed and its real core is complex); §3
  **`productUnifSplits : ProductUnifSplits`**. Compile iterations: `commRingCatIsoToRingEquiv`
  injectivity, retype `p.left` as a map from `Spec ℂ`, explicit `IsIso.epi_of_iso … |>.left_cancellation`,
  `_root_.mul_one` (ambiguous with `MonObj.mul_one`), `calc` for the decomposition `y = ι₁π₁y + ι₂π₂y`.
  Final: 0 errors, `#print axioms` of `pts_eq_of_evalAt`, `kerSub_facts`, `productUnifSplits`:
  `propext, Classical.choice, Quot.sound` (VERIFIED). 16 s.
- §4 S-alg reduction added to `ProductUnif.lean`: new glue Props `ProductUnifDims` (S-alg-1),
  `JacDetDescends` (S-alg-2), `ProductHodgeAdd` (S-alg-3) and
  `productMetrizationOfProductUnif_of : HodgeLatticeTheorem → ProductUnifDims → JacDetDescends →
  ProductHodgeAdd → ProductMetrizationOfProductUnif` (factor metrizations built in the proof;
  `HodgeLatticeTheorem` is the kernel's Prop from `Models.lean`). First compile: 0 errors; 4/4
  `#print axioms` standard (VERIFIED). 54 s.
