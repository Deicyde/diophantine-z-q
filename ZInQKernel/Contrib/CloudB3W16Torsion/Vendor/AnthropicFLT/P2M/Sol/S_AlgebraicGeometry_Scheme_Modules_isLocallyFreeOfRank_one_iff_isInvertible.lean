/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible

set_option autoImplicit false

universe u
open CategoryTheory
open AlgebraicGeometry
-- Source P2M scope referred to a not-yet-declared local namespace; root scope retained.

namespace AlgebraicGeometry
export AlgebraicGeometry (Scheme Scheme.Modules Scheme.Modules.IsLocallyFreeOfRank Scheme.Modules.IsInvertible)
namespace Scheme
export AlgebraicGeometry.Scheme (ringCatSheaf Modules Modules.IsLocallyFreeOfRank Modules.IsInvertible)
namespace Modules
export AlgebraicGeometry.Scheme.Modules (IsLocallyFreeOfRank IsInvertible)
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme
open AlgebraicGeometry

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
