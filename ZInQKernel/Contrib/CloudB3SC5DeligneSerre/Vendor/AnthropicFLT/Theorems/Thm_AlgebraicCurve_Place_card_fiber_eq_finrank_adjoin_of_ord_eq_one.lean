/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_card_fiber_eq_finrank_adjoin_of_ord_eq_one (git blob e7ce8303c1ca85580bd0b8cb7ac07c6f925a49a8, sha256 e03b35313ebe01764c198f74a2f9688d3975dadc7dfe41521a4650ef4cd0b862).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_card_fiber_eq_finrank_adjoin_of_ord_eq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve

theorem AlgebraicCurve.Place.card_fiber_eq_finrank_adjoin_of_ord_eq_one
    (F : Type*) [Field F] [Algebra ℂ F] [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
    {f : F} (htr : Transcendental ℂ f)
    [FiniteDimensional (↥(IntermediateField.adjoin ℂ ({f} : Set F))) F]
    (hrat : ∀ w : Place ℂ F, w.IsRational)
    (hratE : ∀ u : Place ℂ (↥(IntermediateField.adjoin ℂ ({f} : Set F))), u.IsRational)
    (t : ℂ) (w₀ : Place ℂ F) (h₀m : f ∈ w₀.toValuationSubring) (h₀v : w₀.evalAt f = t)
    (hunram : ∀ w : Place ℂ F, f ∈ w.toValuationSubring → w.evalAt f = t →
      w.ord (f - algebraMap ℂ F t) = 1) :
    Nat.card {P : Place ℂ F // f ∈ P.toValuationSubring ∧ P.evalAt f = t}
      = Module.finrank (↥(IntermediateField.adjoin ℂ ({f} : Set F))) F := by
  revert F f htr hrat hratE t w₀ h₀m h₀v hunram
  exact @_root_.P2MW.S_AlgebraicCurve_Place_card_fiber_eq_finrank_adjoin_of_ord_eq_one.solution
