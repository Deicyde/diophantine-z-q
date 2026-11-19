/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_HaarQuotient_lintegral_mul_comp_out_eq_tsum_zpow_mul_setLIntegral_of_mem_normalizer (git blob f36d815570cbba54709527ea5d58a674affcb60d, sha256 c3fd1aa33ecd4b7122a33b923113664274285ac5a2a7f2f98f69d1542d43ad28).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_HaarQuotient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_HaarQuotient_lintegral_mul_comp_out_eq_tsum_zpow_mul_setLIntegral_of_mem_normalizer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem HaarQuotient.lintegral_mul_comp_out_eq_tsum_zpow_mul_setLIntegral_of_mem_normalizer
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (b : G) (hb : ∀ y : G, y ∈ H ↔ b * y * b⁻¹ ∈ H) (D : ℝ≥0∞) (hD₀ : D ≠ 0) (hD : D ≠ ∞)
    (hbD : ∀ F : H → ℝ≥0∞, Measurable F →
      ∫⁻ x, F ⟨b * (x : G) * b⁻¹, (hb (x : G)).mp x.2⟩ ∂μH = D * ∫⁻ x, F x ∂μH)
    (m : G → ℤ) (hm : Measurable m) (hmH : ∀ x ∈ H, ∀ g : G, m (x * g) = m g)
    (hmb : ∀ g : G, m (b * g) = m g + 1)
    (h : G → ℝ≥0∞) (hh : Measurable h) (hhH : ∀ x ∈ H, ∀ g : G, h (x * g) = h g)
    (hhb : ∀ g : G, h (b * g) = h g)
    (Φ : ℤ → ℝ≥0∞) :
    ∫⁻ q, h q.out * Φ (m q.out) ∂(HaarQuotient.measure μ H μH) =
      (∑' n : ℤ, D ^ n * Φ n) *
        ∫⁻ q in {q : MulAction.orbitRel.Quotient H G | m q.out = 0}, h q.out ∂(HaarQuotient.measure μ H μH) := by
  revert G μ H hH μH b hb D hD₀ hD hbD m hm hmH hmb h hh hhH hhb Φ
  exact @_root_.P2MW.S_HaarQuotient_lintegral_mul_comp_out_eq_tsum_zpow_mul_setLIntegral_of_mem_normalizer.solution
