/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_ncard_algHom_comp_eq_preimage_eq_ramificationIndexAlong (git blob cc50ca19c69cd25638e2bf9aa3f2f07fa406f1a4, sha256 865a123fd858f7fd96bd6d2e9067a4961388f1f3d945c8d33bd31a93518b196b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_ncard_algHom_comp_eq_preimage_eq_ramificationIndexAlong

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve

theorem AlgebraicCurve.Place.ncard_algHom_comp_eq_preimage_eq_ramificationIndexAlong
    (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [IsAlgClosed K] [CharZero K] [IsCurveOver K F] [IsCurveOver K F']
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (E : Type*) [Field E] [Algebra K E] [IsAlgClosed E]
    (A : ValuationSubring E) (e : F →ₐ[K] E) (v₀ : Place K F)
    (hev₀ : ∀ f : F, f ∈ v₀.toValuationSubring ↔ e f ∈ A)
    (q : Place K F') (hq : q.restrictAlong φ hφ = v₀) :
    Set.ncard {σ : F' →ₐ[K] E | σ.comp φ = e ∧
        ∀ g : F', g ∈ q.toValuationSubring ↔ σ g ∈ A} =
      q.ramificationIndexAlong φ := by
  revert K F F' hfg φ hφ hfin E A e v₀ hev₀ q hq
  exact @_root_.P2MW.S_AlgebraicCurve_Place_ncard_algHom_comp_eq_preimage_eq_ramificationIndexAlong.solution
