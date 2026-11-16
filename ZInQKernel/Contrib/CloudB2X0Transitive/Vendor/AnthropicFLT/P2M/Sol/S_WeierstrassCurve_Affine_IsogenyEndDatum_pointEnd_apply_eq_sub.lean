/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_WeierstrassCurve_Affine_IsogenyEndDatum_pointEnd_apply_eq_sub
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_Isogeny_ConditionalCurrency
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_pointEnd_apply_eq_sub

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

theorem solution
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {W : WeierstrassCurve.Affine F} [W.IsElliptic] [GenusOnePlaceGate W] [AbelTheorem W]
    (D : IsogenyEndDatum W) (hN : NormFormulaAlong F D.ι D.hfin) (P : W.Point) :
    D.pointEnd hN P
      = (pointEquivPlace (W := W)).symm ((placeOfPoint P).restrictAlong D.ι D.hι)
        - (pointEquivPlace (W := W)).symm ((placeOfPoint (0 : W.Point)).restrictAlong D.ι D.hι) := by

  set Q : W.Point := (pointEquivPlace (W := W)).symm ((placeOfPoint P).restrictAlong D.ι D.hι) with hQ
  set Q₀ : W.Point :=
    (pointEquivPlace (W := W)).symm ((placeOfPoint (0 : W.Point)).restrictAlong D.ι D.hι) with hQ₀
  have hP : (placeOfPoint P).restrictAlong D.ι D.hι = placeOfPoint Q :=
    ((pointEquivPlace (W := W)).apply_symm_apply _).symm
  have h0 : (placeOfPoint (0 : W.Point)).restrictAlong D.ι D.hι = placeOfPoint Q₀ :=
    ((pointEquivPlace (W := W)).apply_symm_apply _).symm

  have hdiv : (Pic0.pushforwardAlongDegZero D.ι D.hι (pointDivisor P) :
      AlgebraicCurve.Divisor F W.FunctionField)
        = Finsupp.single (placeOfPoint Q) 1 - Finsupp.single (placeOfPoint Q₀) 1 := by
    rw [Pic0.coe_pushforwardAlongDegZero, coe_pointDivisor, map_sub,
      pushforwardAlong_single_eq D.ι D.hι, pushforwardAlong_single_eq D.ι D.hι, hP, h0]
  rw [IsogenyEndDatum.pointEnd_apply, pointClass, Pic0.pushforwardAlongHom_mk,
    genusOnePic0Equiv_apply, pic0ToPoint_mk, hdiv, map_sub, divisorSum_single_placeOfPoint,
    divisorSum_single_placeOfPoint, one_smul, one_smul]
