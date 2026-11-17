/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme Scheme.Modules Scheme.Modules.IsLocallyFreeOfRank Scheme.Modules.IsInvertible"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Modules Modules.IsLocallyFreeOfRank Modules.IsInvertible"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "IsLocallyFreeOfRank IsInvertible"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace RankOne

noncomputable def freeOneIsoUnit (Y : Scheme.{u}) :
    (SheafOfModules.free.{u} (ULift.{u} (Fin 1)) : Y.Modules) ≅ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) :=
  Limits.coproductUniqueIso (fun _ : ULift.{u} (Fin 1) => (SheafOfModules.unit Y.ringCatSheaf : Y.Modules))

theorem iff (X : Scheme.{u}) (M : X.Modules) : IsLocallyFreeOfRank 1 M ↔ IsInvertible M := by
  constructor
  · intro h
    refine ⟨fun x => ?_⟩
    obtain ⟨U, hxU, ⟨e⟩⟩ := h.exists_trivialization x
    exact ⟨U, hxU, ⟨e ≪≫ freeOneIsoUnit U.toScheme⟩⟩
  · intro h
    refine ⟨fun x => ?_⟩
    obtain ⟨U, hxU, ⟨e⟩⟩ := h.exists_trivialization x
    exact ⟨U, hxU, ⟨e ≪≫ (freeOneIsoUnit U.toScheme).symm⟩⟩

end RankOne

end AlgebraicGeometry.Scheme.Modules

theorem solution {X : Scheme.{u}} (M : X.Modules) :
    Scheme.Modules.IsLocallyFreeOfRank 1 M ↔ Scheme.Modules.IsInvertible M :=
  AlgebraicGeometry.Scheme.Modules.RankOne.iff X M
