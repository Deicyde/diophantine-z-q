/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_MeasureTheory_differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le (git blob 890999e185f4d8c58828f35b32879d2a0ad0d359, sha256 cedd1b33b17cbb82da6070dda9b7aead3ba3afcb12601b68ec1c4a03cf85275a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_MeasureTheory_differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    {U : Set ℂ} (hU : IsOpen U) (F : ℂ → Y → ℂ)
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (F z) ν)
    (hhol : ∀ a : Y, DifferentiableOn ℂ (fun z => F z a) U)
    (hdom : ∀ z₀ ∈ U, ∃ ε : ℝ, 0 < ε ∧ ∃ M : Y → ℝ, Integrable M ν ∧
      ∀ z ∈ Metric.ball z₀ ε, ∀ a : Y, ‖F z a‖ ≤ M a) :
    DifferentiableOn ℂ (fun z => ∫ a, F z a ∂ν) U := by
  revert Y ν U hU F hmeas hhol hdom
  exact @_root_.P2MW.S_MeasureTheory_differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le.solution
