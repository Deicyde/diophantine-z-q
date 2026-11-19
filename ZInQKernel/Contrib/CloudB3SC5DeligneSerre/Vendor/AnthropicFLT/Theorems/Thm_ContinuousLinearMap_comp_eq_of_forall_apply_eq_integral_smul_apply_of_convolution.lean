/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ContinuousLinearMap_comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution (git blob 7f5913f2a2025ce361b5f262572a3bf1771b8f38, sha256 9fe7de51006de7d7ee8cd5f49d5644eed55c44e6244285364906f55f3aff88f2).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ContinuousLinearMap_comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate

theorem ContinuousLinearMap.comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution
    {C : Type*} [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C] [T2Space C]
    [MeasurableSpace C] [BorelSpace C] (μ : Measure C) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : C →* (H →L[ℂ] H)) (B : ℝ) (hSb : ∀ c : C, ‖S c‖ ≤ B) (hSc : ∀ v : H, Continuous fun c : C => S c v) :
    (∀ (w₁ w₂ : C → ℂ), Continuous w₁ → Continuous w₂ →
      ∀ (A₁ A₂ A₁₂ : H →L[ℂ] H),
        (∀ v : H, A₁ v = ∫ c, (w₁ c) • (S c v) ∂μ) → (∀ v : H, A₂ v = ∫ c, (w₂ c) • (S c v) ∂μ) →
        (∀ v : H, A₁₂ v = ∫ c, (∫ d, w₁ d * w₂ (d⁻¹ * c) ∂μ) • (S c v) ∂μ) →
        A₁.comp A₂ = A₁₂) ∧
    (∀ A : H →L[ℂ] H, (∀ v : H, A v = ∫ c, S c v ∂μ) →
      (∀ v : H, A v = v ↔ ∀ c : C, S c v = v) ∧ A.comp A = A) := by
  revert C μ H S B hSb hSc
  exact @_root_.P2MW.S_ContinuousLinearMap_comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution.solution
