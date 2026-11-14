# dimjac-glue results log

Target: `ModularSplit.DimJac.H0DifferentialsEqHolo` (scratch/modular-split/DimJac.lean), copied verbatim.

## Setup
- 11-14 12:30: copied missing oleans from ~/dzq-wt/modular-split/.lake/build (CloudW07 etc.); `lake build` of
  DimJac imports: success (only Dim.SmoothStalk rebuilt). DimJacOrig.lean (verbatim copy) compiles, axioms standard. VERIFIED.

## Plan (proof outline, all glue)
Φ_U : Γ(Ω,U) → Ω_{F/ℚ} on affine nonempty U via library `kaehlerSectionsEquiv` + `KaehlerDifferential.map ℚ ℚ Γ(U) F`;
glue to Φ : Γ(Ω,X) → Ω_F; injective (Ω_A torsion-free + sheaf locality); image ⊆ holoDiff (valuative criterion center);
image ⊇ holoDiff (stalks are valuation rings + local-global in Γ(U) + sheaf gluing); ℚ-linearity automatic (toRatLinearMap).
