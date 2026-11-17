/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_HaarQuotient (git blob bbd14c338ab42006df197e1c592ac4383421453f, sha256 0e21eb65be3828da1e230faaca2ae6e95726497c9e53ebbe3b31a3d0749ac4b9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.MeasureTheory.Measure.WithDensity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace HaarQuotient

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

def weight (H : Subgroup G) (μH : Measure H) : G → ℝ≥0∞ :=
  open Classical in
  if h : SigmaCompactSpace G ∧ WeaklyLocallyCompactSpace G then
    haveI := h.1
    haveI := h.2
    fun g => ∑' n : ℕ,
      (2⁻¹ : ℝ≥0∞) ^ n *
        (1 + μH (((↑) : H → G) ⁻¹'
          ((CompactExhaustion.choice G (n + 1) : Set G) *
            (CompactExhaustion.choice G (n + 1) : Set G)⁻¹)))⁻¹ *
        (interior (CompactExhaustion.choice G (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) g
  else 0

def density (H : Subgroup G) (μH : Measure H) (g : G) : ℝ≥0∞ :=
  weight H μH g / ∫⁻ x : H, weight H μH ((x : G) * g) ∂μH

def measure (μ : Measure G) (H : Subgroup G) (μH : Measure H) :
    Measure (MulAction.orbitRel.Quotient H G) :=
  Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G)
    (μ.withDensity (density H μH))

end HaarQuotient

end
