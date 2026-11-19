/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_HaarQuotient_setLIntegral_eq_lintegral_setLIntegral_mul_out (git blob cf9a572f9faa1b85166ec2246616130231e3060b, sha256 36771fc8e721ba93f4fcfeacc3c594f9c3c3d4f5e148bbe75fcf6873a5d774cb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.MeasureTheory.Group.FundamentalDomain
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_HaarQuotient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_HaarQuotient_setLIntegral_eq_lintegral_setLIntegral_mul_out

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem HaarQuotient.setLIntegral_eq_lintegral_setLIntegral_mul_out
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (Γ : Subgroup G) (hΓ : Γ ≤ H) [Countable Γ]
    (f : G → ℝ≥0∞) (hf : Measurable f) (hfΓ : ∀ γ ∈ Γ, ∀ g : G, f (γ * g) = f g)
    (S : Set G) (hS : IsFundamentalDomain Γ S μ)
    (T : Set H) (hT : IsFundamentalDomain (Γ.subgroupOf H) T μH) :
    ∫⁻ g in S, f g ∂μ =
      ∫⁻ q, (∫⁻ x in T, f ((x : G) * q.out) ∂μH) ∂(HaarQuotient.measure μ H μH) := by
  revert G μ H hH μH Γ hΓ f hf hfΓ S hS T hT
  exact @_root_.P2MW.S_HaarQuotient_setLIntegral_eq_lintegral_setLIntegral_mul_out.solution
