/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_variableChange_eq
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_cyclicQuotientJ_variableChange_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open WeierstrassCurve

universe u in

theorem WeierstrassCurve.cyclicQuotientJ_variableChange_eq
    {L : Type u} [Field L] [DecidableEq L] (C : VariableChange L) (E : WeierstrassCurve L)
    (H : AddSubgroup E.toAffine.Point) (H' : AddSubgroup (C • E).toAffine.Point)
    (hH' : ∀ P, P ∈ H' ↔ WeierstrassCurve.Affine.Point.vcFun C E P ∈ H)
    (N : ℕ) (hN : (N : L) ≠ 0) :
    (C • E).cyclicQuotientJ H' N = E.cyclicQuotientJ H N := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_cyclicQuotientJ_variableChange_eq.solution
