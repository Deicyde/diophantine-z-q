/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_MeasureTheory_finiteDimensional_and_finrank_le_of_forall_norm_le_mul_eLpNorm_restrict (git blob a0725ed117bce70aef8629a5f483f7b4797f9e01, sha256 fdfd03fa80eaa1453ee57317a82244a62b303d114de6d75d98e350562b465bba).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_MeasureTheory_finiteDimensional_and_finrank_le_of_forall_norm_le_mul_eLpNorm_restrict

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

theorem MeasureTheory.finiteDimensional_and_finrank_le_of_forall_norm_le_mul_eLpNorm_restrict
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (s : Set X) (hsm : MeasurableSet s) (hs : μ s ≠ ⊤)
    (V : Submodule ℂ (X → ℂ))
    (hmeas : ∀ φ ∈ V, AEStronglyMeasurable φ (μ.restrict s))
    (hinj : ∀ φ ∈ V, (∀ x ∈ s, φ x = 0) → φ = 0)
    (C : ℝ)
    (hsup : ∀ φ ∈ V, ∀ x ∈ s, ‖φ x‖ ≤ C * (eLpNorm φ 2 (μ.restrict s)).toReal) :
    FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℝ) ≤ C ^ 2 * (μ s).toReal := by
  revert X μ s hsm hs V hmeas hinj C hsup
  exact @_root_.P2MW.S_MeasureTheory_finiteDimensional_and_finrank_le_of_forall_norm_le_mul_eLpNorm_restrict.solution
