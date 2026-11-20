/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_HaarQuotient_lintegral_density_mul_eq_one (git blob 7f4da2f24bb94fb87ce1090f8d703152ccb70b19, sha256 f3893b2f560b5ac023a8dcb89f16d494d106fa9479b95ad7043d887ebd9f2d50).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_HaarQuotient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_HaarQuotient_lintegral_density_mul_eq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory

theorem HaarQuotient.lintegral_density_mul_eq_one
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] (g : G) :
    ∫⁻ x : H, HaarQuotient.density H μH ((x : G) * g) ∂μH = 1 := by
  revert G H hH μH g
  exact @_root_.P2MW.S_HaarQuotient_lintegral_density_mul_eq_one.solution
