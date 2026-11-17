/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_MeasureTheory_tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le (git blob 77510358a63ebbf7a341c061ce78a0b790c95828, sha256 d7d0789b1dfe94a037880af3492455877534395e8d81c1dbff21d31a26bf07eb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Instances.ENNReal.Lemmas
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_MeasureTheory_tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory Filter
open scoped ENNReal Topology

theorem MeasureTheory.tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι} [l.IsCountablyGenerated]
    (F G : ι → α → ℝ≥0∞) (g : α → ℝ≥0∞)
    (hF : ∀ i, AEMeasurable (F i) μ) (hG : ∀ i, AEMeasurable (G i) μ)
    (hFG : ∀ i, ∀ᵐ x ∂μ, F i x ≤ G i x)
    (hF0 : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 0))
    (hGg : ∀ᵐ x ∂μ, Tendsto (fun i => G i x) l (𝓝 (g x)))
    (hg : ∫⁻ x, g x ∂μ ≠ ∞)
    (hlim : limsup (fun i => ∫⁻ x, G i x ∂μ) l ≤ ∫⁻ x, g x ∂μ) :
    Tendsto (fun i => ∫⁻ x, F i x ∂μ) l (𝓝 0) := by
  revert α ι μ l F G g hF hG hFG hF0 hGg hg hlim
  exact @_root_.P2MW.S_MeasureTheory_tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le.solution
