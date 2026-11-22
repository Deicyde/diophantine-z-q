/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_stepCurve_stepSubgroup_two_eq
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_VeluPointMap2
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_stepCurve_stepSubgroup_two_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open WeierstrassCurve

universe u in

theorem WeierstrassCurve.stepCurve_stepSubgroup_two_eq
    {L : Type u} [Field L] [DecidableEq L] (E : WeierstrassCurve L) (h2 : (2 : L) ≠ 0)
    (H : AddSubgroup E.toAffine.Point) [IsAddCyclic H] [Finite H]
    {x₀ y₀ : L} (hns : E.toAffine.Nonsingular x₀ y₀) (hQH : (.some x₀ y₀ hns : E.toAffine.Point) ∈ H)
    (hgy : E.veluGy x₀ y₀ = 0) (hΔ : (E.veluQuotient2 x₀ y₀).Δ ≠ 0)
    (φ : E.toAffine.Point →+ (E.veluQuotient2 x₀ y₀).toAffine.Point)
    (hφ : ⇑φ = veluPointMap2 h2 hns.1 hgy hΔ) :
    (⟨E.stepCurve H 2, E.stepSubgroup H 2⟩ : Σ V : WeierstrassCurve L, AddSubgroup V.toAffine.Point) =
      ⟨E.veluQuotient2 x₀ y₀, H.map φ⟩ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_stepCurve_stepSubgroup_two_eq.solution
