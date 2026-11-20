/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_sum_fiber_ord_eq_finrank (git blob bf14e5b484531eb237d0d3b46aa6dadea0ff7cea, sha256 2d406b29103ee64a1c70780031623eade7a3b9d6843c54068a88ce21d7d4804d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_sum_fiber_ord_eq_finrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve IntermediateField

theorem AlgebraicCurve.Place.sum_fiber_ord_eq_finrank {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    {x : F} (htr : Transcendental ℂ x) [FiniteDimensional (↥(adjoin ℂ ({x} : Set F))) F] :
    (∀ (b : ℂ) (s : Finset (Place ℂ F)),
      (∀ w : Place ℂ F, w ∈ s ↔ x ∈ w.toValuationSubring ∧ Place.evalAt w x = b) →
      ∑ w ∈ s, (w.ord (x - algebraMap ℂ F b)).toNat = Module.finrank (↥(adjoin ℂ ({x} : Set F))) F) ∧
    (∀ s : Finset (Place ℂ F), (∀ w : Place ℂ F, w ∈ s ↔ x ∉ w.toValuationSubring) →
      ∑ w ∈ s, (w.ord x⁻¹).toNat = Module.finrank (↥(adjoin ℂ ({x} : Set F))) F) := by
  revert F x htr
  exact @_root_.P2MW.S_AlgebraicCurve_Place_sum_fiber_ord_eq_finrank.solution
