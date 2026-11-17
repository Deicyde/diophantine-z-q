/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_MeasureTheory_exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le (git blob bfc1d2c745e344fdae4113b44934ed17d49d7da0, sha256 0b98f6b1388a78ef2cec1653a67b9f931e7d84eec1bbe963ccb2f40ff7051428).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_MeasureTheory_exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory Topology Filter Set BoundedContinuousFunction
open scoped ENNReal NNReal

theorem MeasureTheory.exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {ι : Type*} (u : ι → X → E) (μ : Measure X) [IsFiniteMeasure μ]
    (p : ℝ≥0∞) (hp₁ : 1 ≤ p) (hp : p ≠ ∞)
    (htight : ∀ η : ℝ≥0∞, 0 < η → ∃ K : Set X, IsCompact K ∧ μ Kᶜ < η)
    (hequi : Equicontinuous u)
    (hpt : ∀ x, ∃ C₀ : ℝ, ∀ i, ‖u i x‖ ≤ C₀)
    (C : ℝ) (hbound : ∀ i, ∀ᵐ x ∂μ, ‖u i x‖ ≤ C)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ s : Finset ι, ∀ i, ∃ j ∈ s, eLpNorm (u i - u j) p μ < ε := by
  revert X E ι u μ p hp₁ hp htight hequi hpt C hbound ε hε
  exact @_root_.P2MW.S_MeasureTheory_exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le.solution
