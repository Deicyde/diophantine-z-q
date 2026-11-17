/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange

universe u

open CategoryTheory AlgebraicGeometry Opposite AlgebraicGeometry.Scheme.Modules

theorem solution
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] (N : X.Modules)
    (V : X.Opens) (hV : V ≤ j.opensRange) :
    Function.Bijective (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N).app V) := by
  have hfac := Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction j) (pullbackPushforwardAdjunction j) N
  have hfac' := congrArg (fun t => Hom.app t V) hfac.symm

  have heq : j ''ᵁ j ⁻¹ᵁ V = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hV]
  have h2 : (homOfLE (j.image_preimage_le V)).op = eqToHom (congrArg op heq.symm) := Subsingleton.elim _ _
  have hiso1 : IsIso (N.presheaf.map (homOfLE (j.image_preimage_le V)).op) := by
    rw [h2]
    exact ⟨N.presheaf.map (eqToHom (congrArg op heq)), by simp [eqToHom_map], by simp [eqToHom_map]⟩
  have hiso2 : IsIso ((((restrictAdjunction j).leftAdjointUniq (pullbackPushforwardAdjunction j)).hom.app N).app
      (j ⁻¹ᵁ V)) := inferInstance
  have hiso := @IsIso.comp_isIso _ _ _ _ _ _ _ hiso1 hiso2
  rw [← ConcreteCategory.isIso_iff_bijective]

  revert hiso
  refine fun hiso => ?_
  rw [hfac']
  exact hiso
