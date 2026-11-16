/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_WeierstrassCurve_Affine_algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_Affine_placeOfPoint_some_eq_ofHeightOneSpectrum
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_Affine_FunctionField_exists_eq_valuationSubring_of_X_mem
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_WeierstrassCurve_Affine_algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero
attribute [-instance] WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral
attribute [-simp] WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal

set_option autoImplicit false

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine

universe u

theorem solution
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] :
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (Polynomial.C Polynomial.X))
      ∉ (placeOfPoint (0 : W.Point)).toValuationSubring := by
  intro hXO
  haveI : IsDedekindDomain W.CoordinateRing := CoordinateRing.isDedekindDomain W
  obtain ⟨w, hw⟩ := WeierstrassCurve.Affine.FunctionField.exists_eq_valuationSubring_of_X_mem W
    (placeOfPoint (0 : W.Point)).toValuationSubring (placeOfPoint (0 : W.Point)).ne_top'
    (placeOfPoint (0 : W.Point)).algebraMap_mem' hXO
  haveI := w.isPrime
  obtain ⟨a, b, hab, hwI⟩ := CoordinateRing.exists_eq_XYIdeal (W := W) (P := w.asIdeal) w.ne_bot
  have hns : W.Nonsingular a b := (equation_iff_nonsingular (W := W)).mp hab
  have h1 : placeOfPoint (Point.some a b hns) = Place.ofHeightOneSpectrum (K := F) w :=
    WeierstrassCurve.Affine.placeOfPoint_some_eq_ofHeightOneSpectrum hns w hwI
  have h2 : placeOfPoint (0 : W.Point) = Place.ofHeightOneSpectrum (K := F) w :=
    AlgebraicCurve.Place.ext (by rw [Place.ofHeightOneSpectrum_toValuationSubring]; exact hw)
  have h3 : (Point.some a b hns : W.Point) = 0 :=
    (pointEquivPlace (W := W)).injective (by rw [pointEquivPlace_apply, pointEquivPlace_apply, h1, h2])
  exact absurd h3 (by rintro ⟨⟩)
