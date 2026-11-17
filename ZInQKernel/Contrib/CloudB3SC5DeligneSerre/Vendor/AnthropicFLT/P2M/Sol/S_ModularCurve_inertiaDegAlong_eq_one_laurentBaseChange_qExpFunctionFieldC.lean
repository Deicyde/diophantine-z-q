/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC (git blob 10f3deacdd010516ce3ae286f578549b8aafa387, sha256 9203c3702f68af1bb9a4b7aa57057e4ef078f2503189ee6bbbd3386c0843a352).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve
namespace AlgebraicCurve
end AlgebraicCurve
namespace P2MW.S_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC.AlgebraicCurve
end P2MW.S_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC.AlgebraicCurve

namespace P2MW.S_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC

set_option autoImplicit false

open _root_.ModularCurve
open _root_.AlgebraicCurve
open _root_.P2MW.S_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC.AlgebraicCurve
open scoped MatrixGroups

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place algebraAlong isScalarTower_along isIntegral_along)
namespace InertiaOne
open _root_.AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem inertiaDegAlong_eq_one_of_deg_target_eq_one (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (hw : w.deg = 1) : w.inertiaDegAlong φ hφ = 1 := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  have h : (w.restrict F).deg * w.inertiaDeg F = 1 := hw ▸ w.deg_restrict_mul_inertiaDeg
  exact Nat.eq_one_of_mul_eq_one_left h

end AlgebraicCurve.InertiaOne

theorem solution
    {L : Type*} [Field L] [Algebra ℚ L] [IsAlgClosed L]
    {F : Type*} [Field F] [Algebra L F]
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (φ : F →ₐ[L] ↥(ModularCurve.laurentBaseChange L F₀))
    (hφ : φ.toRingHom.IsIntegral)
    (W : AlgebraicCurve.Place L ↥(ModularCurve.laurentBaseChange L F₀)) :
    W.inertiaDegAlong φ hφ = 1 :=
  AlgebraicCurve.InertiaOne.inertiaDegAlong_eq_one_of_deg_target_eq_one φ hφ W
    (ModularCurve.place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC L Γ hT F₀ hF W)
