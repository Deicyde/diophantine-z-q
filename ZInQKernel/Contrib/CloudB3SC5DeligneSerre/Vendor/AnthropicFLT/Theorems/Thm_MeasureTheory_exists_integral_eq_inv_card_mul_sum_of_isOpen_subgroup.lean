/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_MeasureTheory_exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup (git blob da8059ebe4994aa79525f13406cb6db098d904f0, sha256 9871e5d4b46ae97f010028aad2e2a1a5a0ee290bf81183006b7dde07a037966c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_MeasureTheory_exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

theorem MeasureTheory.exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (H : Subgroup K) (hH : IsOpen (H : Set K)) :
    ∃ (n : ℕ) (r : Fin n → K), H.index = n ∧ 0 < n ∧
      (∀ v : K, ∃ i, (r i)⁻¹ * v ∈ H) ∧
      (∀ i j, (r i)⁻¹ * r j ∈ H → i = j) ∧
      ∀ h : K → ℂ, (∀ v : K, ∀ w ∈ H, h (v * w) = h v) →
        ∫ v, h v ∂μ = (n : ℂ)⁻¹ * ∑ i, h (r i) := by
  revert K μ H hH
  exact @_root_.P2MW.S_MeasureTheory_exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup.solution
