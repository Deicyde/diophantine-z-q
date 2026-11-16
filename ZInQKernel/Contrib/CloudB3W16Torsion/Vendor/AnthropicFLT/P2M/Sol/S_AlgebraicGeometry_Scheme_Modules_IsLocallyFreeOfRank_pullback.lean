/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback

set_option autoImplicit false

universe u
open CategoryTheory
open AlgebraicGeometry
open P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry

namespace AlgebraicGeometry
export AlgebraicGeometry (morphismRestrict_ι Scheme.Modules.pullback Scheme Scheme.Modules Scheme.Modules.IsLocallyFreeOfRank)
namespace Scheme
export AlgebraicGeometry.Scheme (Modules.pullback Modules.pullbackCongr Modules Opens Modules.pullbackComp Modules.IsLocallyFreeOfRank)
namespace Modules
export AlgebraicGeometry.Scheme.Modules (pullback pullbackCongr pullbackComp IsLocallyFreeOfRank)
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme
open AlgebraicGeometry

scoped instance opensMap_final_of_hom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (TopologicalSpace.Opens.map f.base).Final :=
  CategoryTheory.final_of_representablyFlat _

noncomputable def pullbackFreeIso {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Type u) :
    (Modules.pullback f).obj (SheafOfModules.free.{u} I) ≅ SheafOfModules.free.{u} I :=
  SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I

namespace IsLocallyFreeOfRank p2m_export "AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank" "exists_trivialization" end IsLocallyFreeOfRank
open scoped AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank in
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



theorem solution
    {X Y : Scheme.{u}} (ψ : X ⟶ Y) {n : ℕ} {E : Y.Modules}
    (hE : Scheme.Modules.IsLocallyFreeOfRank n E) :
    Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pullback ψ).obj E) :=
  AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.pullback' ψ hE
