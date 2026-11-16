/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_Affine_IsogenyEndDatum_pointEnd_apply_eq_sub
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_Isogeny_ConditionalCurrency
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_Affine_IsogenyEndDatum_pointEnd_apply_eq_sub

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u
theorem WeierstrassCurve.Affine.IsogenyEndDatum.pointEnd_apply_eq_sub
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {W : WeierstrassCurve.Affine F} [W.IsElliptic] [GenusOnePlaceGate W] [AbelTheorem W]
    (D : IsogenyEndDatum W) (hN : NormFormulaAlong F D.ι D.hfin) (P : W.Point) :
    D.pointEnd hN P
      = (pointEquivPlace (W := W)).symm ((placeOfPoint P).restrictAlong D.ι D.hι)
        - (pointEquivPlace (W := W)).symm ((placeOfPoint (0 : W.Point)).restrictAlong D.ι D.hι) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_pointEnd_apply_eq_sub.solution
