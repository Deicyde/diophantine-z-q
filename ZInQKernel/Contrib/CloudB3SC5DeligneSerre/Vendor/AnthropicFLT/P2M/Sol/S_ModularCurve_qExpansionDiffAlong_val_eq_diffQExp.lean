/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_qExpansionDiffAlong_val_eq_diffQExp (git blob 1e73704ef7173370d00b5f660946bff04506bae9, sha256 8b6f74541e85784ef29965927ad9d71c3b9fefe3cb3607cee41843e52f3c310d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpansionDiff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_HeckeDifferential
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_theta_coeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_eq_qExpansionDiffAlong_of_isQExpansionDiffAlong

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace KaehlerDifferential
end KaehlerDifferential
namespace ModularCurve
end ModularCurve
namespace P2MW.S_ModularCurve_qExpansionDiffAlong_val_eq_diffQExp.ModularCurve
end P2MW.S_ModularCurve_qExpansionDiffAlong_val_eq_diffQExp.ModularCurve

namespace P2MW.S_ModularCurve_qExpansionDiffAlong_val_eq_diffQExp

set_option autoImplicit false

open _root_.KaehlerDifferential
open _root_.ModularCurve
open _root_.P2MW.S_ModularCurve_qExpansionDiffAlong_val_eq_diffQExp.ModularCurve

section Engine

private theorem qEuler_eq_thetaL {L : Type*} [Field L] (f : LaurentSeries L) :
    qEuler L f = thetaL L f := by
  ext n
  rw [qEuler_coeff, thetaL_apply, theta_coeff, zsmul_eq_mul]

private theorem isQExpansionDiffAlong_restrictScalars {L : Type*} [Field L]
    (F : IntermediateField L (LaurentSeries L)) :
    IsQExpansionDiffAlong F.val ((diffQExp F).restrictScalars L) := by
  refine ⟨fun x => ?_, fun f ω => ?_⟩
  · show diffQExp F (D L F x) = thetaL L (F.val x)
    rw [diffQExp_D, qEuler_eq_thetaL]
    rfl
  · exact (diffQExp F).map_smul f ω

end Engine

namespace ModularCurve export _root_.ModularCurve (thetaL thetaL_apply IsQExpansionDiffAlong qExpansionDiffAlong qEuler qEuler_coeff diffQExp diffQExp_D diffQExpBar modularFunctionFieldBar theta_coeff eq_qExpansionDiffAlong_of_isQExpansionDiffAlong) end ModularCurve
open scoped _root_.ModularCurve in

private theorem ModularCurve.qExpansionDiffAlong_val_eq_diffQExp {L : Type*} [Field L]
    (F : IntermediateField L (LaurentSeries L)) (ω : Ω[F⁄L]) :
    qExpansionDiffAlong F.val ω = diffQExp F ω := by
  have h := eq_qExpansionDiffAlong_of_isQExpansionDiffAlong F.val
    (isQExpansionDiffAlong_restrictScalars F)
  exact (DFunLike.congr_fun h ω).symm

open scoped _root_.ModularCurve in

private theorem ModularCurve.qExpansionDiffAlong_val_eq_diffQExpBar (N : ℕ) [NeZero N]
    (ω : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ]) :
    qExpansionDiffAlong (modularFunctionFieldBar N).val ω = diffQExpBar N ω :=
  qExpansionDiffAlong_val_eq_diffQExp (modularFunctionFieldBar N) ω

open scoped _root_.ModularCurve in

private theorem ModularCurve.restrictScalars_diffQExpBar_eq_qExpansionDiffAlong (N : ℕ) [NeZero N] :
    (diffQExpBar N).restrictScalars (AlgebraicClosure ℚ) =
      qExpansionDiffAlong (modularFunctionFieldBar N).val :=
  LinearMap.ext fun ω => (qExpansionDiffAlong_val_eq_diffQExpBar N ω).symm

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_qExpansionDiffAlong_val_eq_diffQExp.ModularCurve in

theorem solution {L : Type*} [Field L]
    (F : IntermediateField L (LaurentSeries L)) (ω : Ω[F⁄L]) :
    qExpansionDiffAlong F.val ω = diffQExp F ω :=
  ModularCurve.qExpansionDiffAlong_val_eq_diffQExp F ω

#print axioms solution
