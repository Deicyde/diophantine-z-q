/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "morphismRestrict_ι Scheme.Modules.pullback Scheme Scheme.Modules Scheme.Modules.IsLocallyFreeOfRank"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.pullback Modules.pullbackCongr Modules Opens Modules.pullbackComp Modules.IsLocallyFreeOfRank"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback pullbackCongr pullbackComp IsLocallyFreeOfRank"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

scoped instance opensMap_final_of_hom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (TopologicalSpace.Opens.map f.base).Final :=
  CategoryTheory.final_of_representablyFlat _

noncomputable def pullbackFreeIso {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Type u) :
    (Modules.pullback f).obj (SheafOfModules.free.{u} I) ≅ SheafOfModules.free.{u} I :=
  SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I

namespace IsLocallyFreeOfRank p2m_export "AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank" "exists_trivialization" end IsLocallyFreeOfRank
p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank" in
theorem IsLocallyFreeOfRank.pullback' {X Y : Scheme.{u}} (ψ : X ⟶ Y) {n : ℕ} {E : Y.Modules}
    (hE : IsLocallyFreeOfRank n E) :
    IsLocallyFreeOfRank n ((Modules.pullback ψ).obj E) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hU, ⟨eU⟩⟩ := hE.exists_trivialization (ψ.base x)
  refine ⟨ψ ⁻¹ᵁ U, hU, ⟨?_⟩⟩
  have hfact : (ψ ⁻¹ᵁ U).ι ≫ ψ = (ψ ∣_ U) ≫ U.ι := (morphismRestrict_ι ψ U).symm
  exact (Modules.pullbackComp _ _).app E ≪≫ (Modules.pullbackCongr hfact).app E ≪≫
    ((Modules.pullbackComp _ _).app E).symm ≪≫ (Modules.pullback (ψ ∣_ U)).mapIso eU ≪≫
    pullbackFreeIso (ψ ∣_ U) (ULift.{u} (Fin n))

end AlgebraicGeometry.Scheme.Modules
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry.Scheme.Modules"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry"

theorem solution
    {X Y : Scheme.{u}} (ψ : X ⟶ Y) {n : ℕ} {E : Y.Modules}
    (hE : Scheme.Modules.IsLocallyFreeOfRank n E) :
    Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pullback ψ).obj E) :=
  AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.pullback' ψ hE
