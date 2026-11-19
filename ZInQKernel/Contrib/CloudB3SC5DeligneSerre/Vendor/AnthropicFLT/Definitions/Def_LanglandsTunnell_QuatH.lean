/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_LanglandsTunnell_QuatH (git blob 3d4cf2ef09bf52389314a8704e505b3026746d49, sha256 0fb56be9373be4f25d750f1fb3f5f0efed1a0a9a37798910d999c884b2b30e4d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_SylowH
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.NumberField.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

namespace LanglandsTunnell

open NumberField FLT.ExplicitLift LanglandsTunnell.Lift48
open scoped MatrixGroups

variable {L : Type} [Field L] [NumberField L]

abbrev fixFld (H : Subgroup (L ≃ₐ[ℚ] L)) : IntermediateField ℚ L :=
  FixedPoints.intermediateField (↥H)

theorem fixFld_le_fixFld_of_le {H H' : Subgroup (L ≃ₐ[ℚ] L)} (h : H' ≤ H) :
    fixFld H ≤ fixFld H' := by
  intro x hx
  rw [fixFld, FixedPoints.mem_intermediateField_iff] at hx ⊢
  exact fun g => hx ⟨g.1, h g.2⟩

def detKer (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) : Subgroup (L ≃ₐ[ℚ] L) :=
  (Matrix.GeneralLinearGroup.det.comp e.toMonoidHom).ker

theorem mem_detKer_iff (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) (γ : L ≃ₐ[ℚ] L) :
    γ ∈ detKer e ↔
      ((e γ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 := by
  rw [detKer, MonoidHom.mem_ker, MonoidHom.comp_apply, ← Units.val_eq_one]
  rfl

instance detKer_normal (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) : (detKer e).Normal := by
  unfold detKer; infer_instance

def quatH (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) : Subgroup (L ≃ₐ[ℚ] L) :=
  sylowH e ⊓ detKer e

theorem quatH_le_sylowH (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) : quatH e ≤ sylowH e :=
  inf_le_left

theorem quatH_le_detKer (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) : quatH e ≤ detKer e :=
  inf_le_right

theorem fixFld_sylowH_le_fixFld_quatH (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) :
    fixFld (sylowH e) ≤ fixFld (quatH e) :=
  fixFld_le_fixFld_of_le (quatH_le_sylowH e)

theorem fixFld_detKer_le_fixFld_quatH (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) :
    fixFld (detKer e) ≤ fixFld (quatH e) :=
  fixFld_le_fixFld_of_le (quatH_le_detKer e)

section TowerInstances

variable (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3))

noncomputable instance algebra_fixFldSylowH_fixFldQuatH :
    Algebra ↥(fixFld (sylowH e)) ↥(fixFld (quatH e)) :=
  (IntermediateField.inclusion (fixFld_sylowH_le_fixFld_quatH e)).toRingHom.toAlgebra

instance isScalarTower_rat_fixFldSylowH_fixFldQuatH :
    IsScalarTower ℚ ↥(fixFld (sylowH e)) ↥(fixFld (quatH e)) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

instance isScalarTower_fixFldSylowH_fixFldQuatH_L :
    IsScalarTower ↥(fixFld (sylowH e)) ↥(fixFld (quatH e)) L :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (IntermediateField.coe_inclusion (fixFld_sylowH_le_fixFld_quatH e) x).symm)

noncomputable instance algebra_fixFldDetKer_fixFldQuatH :
    Algebra ↥(fixFld (detKer e)) ↥(fixFld (quatH e)) :=
  (IntermediateField.inclusion (fixFld_detKer_le_fixFld_quatH e)).toRingHom.toAlgebra

instance isScalarTower_rat_fixFldDetKer_fixFldQuatH :
    IsScalarTower ℚ ↥(fixFld (detKer e)) ↥(fixFld (quatH e)) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

instance isScalarTower_fixFldDetKer_fixFldQuatH_L :
    IsScalarTower ↥(fixFld (detKer e)) ↥(fixFld (quatH e)) L :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (IntermediateField.coe_inclusion (fixFld_detKer_le_fixFld_quatH e) x).symm)

end TowerInstances

section SynthProbe

variable (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3))
noncomputable example : Algebra (𝓞 ↥(fixFld (sylowH e))) (𝓞 ↥(fixFld (quatH e))) := inferInstance
noncomputable example :
    Algebra.IsIntegral (𝓞 ↥(fixFld (sylowH e))) (𝓞 ↥(fixFld (quatH e))) := inferInstance
noncomputable example : Algebra (𝓞 ↥(fixFld (detKer e))) (𝓞 ↥(fixFld (quatH e))) := inferInstance
noncomputable example :
    Algebra.IsIntegral (𝓞 ↥(fixFld (detKer e))) (𝓞 ↥(fixFld (quatH e))) := inferInstance
end SynthProbe

end LanglandsTunnell
