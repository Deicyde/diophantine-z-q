# dimjac-glue results log

Target: `ModularSplit.DimJac.H0DifferentialsEqHolo` (scratch/modular-split/DimJac.lean), copied verbatim.

## Setup
- 11-14 12:30: copied missing oleans from ~/dzq-wt/modular-split/.lake/build (CloudW07 etc.); `lake build` of
  DimJac imports: success (only Dim.SmoothStalk rebuilt). DimJacOrig.lean (verbatim copy) compiles, axioms standard. VERIFIED.

## Plan (proof outline, all glue)
Φ_U : Γ(Ω,U) → Ω_{F/ℚ} on affine nonempty U via library `kaehlerSectionsEquiv` + `KaehlerDifferential.map ℚ ℚ Γ(U) F`;
glue to Φ : Γ(Ω,X) → Ω_F; injective (Ω_A torsion-free + sheaf locality); image ⊆ holoDiff (valuative criterion center);
image ⊇ holoDiff (stalks are valuation rings + local-global in Γ(U) + sheaf gluing); ℚ-linearity automatic (toRatLinearMap).

## Results
- 11-14 ~14:00 `scratch/dimjac-glue/DimJacGlue.lean` compiles (lake env lean, ~10 s), no sorry:
  `ModularSplit.DimJac.h0DifferentialsEqHolo_of_valuationCenter : ValuationCenter → H0DifferentialsEqHolo`
  (statement of H0DifferentialsEqHolo copied verbatim), axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
  Proved along the way (VERIFIED, compiled): Φ_U well defined and injective (`kaehlerToFractionFieldInjective`:
  Ω_A → Ω_K injective for A smooth domain over ℚ); restriction compatibility; global Φ; injectivity by sheaf
  locality; gluing; image ⊆ holoDiff from ValuationCenter; stalks at closed points are valuation rings
  (from kernel `finrank_cotangentSpace_of_smoothOfRelativeDimension` + Mathlib DVR TFAE); closed points from
  maximal ideals (Jacobson); local–global step; surjectivity onto holoDiff; ℚ-linearity via map_rat_smul.
- Remaining named glue: `DimJacGlue.ValuationCenter` (center of a place on a proper integral ℚ-scheme;
  valuative criterion).
- 11-14 12:48 `valuationCenter : ValuationCenter` proved (Mathlib `UniversallyClosed.eq_valuativeCriterion`,
  `Scheme.preimage_eq_top_of_closedPoint_mem`, `fromSpecStalk_app`, `ΓSpecIso_naturality`). VERIFIED (compiled).
- 11-14 12:49 `ModularSplit.DimJac.h0DifferentialsEqHolo : H0DifferentialsEqHolo` (no hypotheses) and
  `ModularSplit.DimJac.dimJacobianEqGenus : ZInQ.Contrib.CurvesG.DimJacobianEqGenus` (modular-split's
  `dimJacobianEqGenus_of_glue` copied verbatim and applied). Axioms of both: [propext, Classical.choice, Quot.sound].
  Statement of H0DifferentialsEqHolo checked verbatim against scratch/modular-split/DimJac.lean by diff. VERIFIED.
  Check command: `lake env lean scratch/dimjac-glue/DimJacGlue.lean` (~10 s once CloudW07 oleans are built).
- Literature leaves used: none. Named glue left open: none.
