/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_MeasureTheory_measure_biUnion_finset_image_mul_right_lt_top (git blob 0b569172fac2b1ecab40cac1401acc9cee2e98e0, sha256 d3e15b25674d9565703882672e58d9121f072978152ddb72b562109a2fb19ae3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_MeasureTheory_measure_biUnion_finset_image_mul_right_lt_top

set_option autoImplicit false

open MeasureTheory

theorem solution
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulRightInvariant]
    (s : Set G) (hs : μ s < ⊤) (T : Finset G) :
    μ (⋃ x ∈ T, (· * x) '' s) < ⊤ := by
  refine lt_of_le_of_lt (measure_biUnion_finset_le T _) ?_
  refine ENNReal.sum_lt_top.mpr fun x _ => ?_
  have : (· * x) '' s = (· * x⁻¹) ⁻¹' s := by
    ext g; simp [Set.mem_preimage]
  rw [this, measure_preimage_mul_right]
  exact hs
