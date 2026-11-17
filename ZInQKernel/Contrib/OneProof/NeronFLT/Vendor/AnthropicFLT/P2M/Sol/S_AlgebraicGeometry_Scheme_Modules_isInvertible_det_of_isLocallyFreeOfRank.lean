/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isInvertible_det_of_isLocallyFreeOfRank
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesDet
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_exteriorPower_iso_exteriorPower_pullback
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_exteriorPower_free_iso_unit
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isInvertible_det_of_isLocallyFreeOfRank
attribute [-simp] PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution {X : Scheme.{u}} {n : ℕ} {M : X.Modules}
    (hM : Scheme.Modules.IsLocallyFreeOfRank n M) :
    Scheme.Modules.IsInvertible (Scheme.Modules.det n M) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hxU, ⟨e⟩⟩ := hM.exists_trivialization x
  obtain ⟨e₁⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_pullback_exteriorPower_iso_exteriorPower_pullback n U M
  obtain ⟨e₂⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_exteriorPower_free_iso_unit (U : Scheme.{u}) n
  exact ⟨U, hxU, ⟨e₁ ≪≫ (Scheme.Modules.exteriorPower (U : Scheme.{u}) n).mapIso e ≪≫ e₂⟩⟩
