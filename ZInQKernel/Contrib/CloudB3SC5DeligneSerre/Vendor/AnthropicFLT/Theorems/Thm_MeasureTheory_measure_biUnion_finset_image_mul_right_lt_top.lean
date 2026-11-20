/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_MeasureTheory_measure_biUnion_finset_image_mul_right_lt_top (git blob 452f798c5cdec13fc3a2aeb9566b2e6dc36851e6, sha256 6d73f8b5387dbc032dcce3bfc21cbf57ce997230a85985f8baab8955ae1e46ba).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_MeasureTheory_measure_biUnion_finset_image_mul_right_lt_top

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.measure_biUnion_finset_image_mul_right_lt_top
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulRightInvariant]
    (s : Set G) (hs : μ s < ⊤) (T : Finset G) :
    μ (⋃ x ∈ T, (· * x) '' s) < ⊤ := by
  revert G μ s hs T
  exact @_root_.P2MW.S_MeasureTheory_measure_biUnion_finset_image_mul_right_lt_top.solution
