/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_forall_exists_opens. Apache-2.0.
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

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_forall_exists_opens

universe u
open CategoryTheory
open AlgebraicGeometry
-- Source P2M scope referred to a not-yet-declared local namespace; root scope retained.
open Opposite
open AlgebraicGeometry.Scheme.Modules
-- Source P2M scope referred to a not-yet-declared local namespace; root scope retained.

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme.Modules.pullback Scheme Scheme.Modules Scheme.Modules.IsLocallyFreeOfRank)
namespace Scheme
export _root_.AlgebraicGeometry.Scheme (Modules.pullback Modules Opens Modules.IsLocallyFreeOfRank)
namespace Modules
export _root_.AlgebraicGeometry.Scheme.Modules (pullback pullbackCongr pullbackComp IsLocallyFreeOfRank)
open AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open AlgebraicGeometry

theorem opensMap_final' {X Y : Scheme.{u}} (f : X ⟶ Y) : (TopologicalSpace.Opens.map f.base).Final :=
  CategoryTheory.final_of_representablyFlat _

noncomputable def pullbackFreeIso' {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Type u) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.free.{u} I) ≅ SheafOfModules.free.{u} I :=
  haveI := opensMap_final' f
  SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I
end AlgebraicGeometry.Scheme.Modules
-- Deferred source P2M scope: open the local namespaces once declared.
open _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_forall_exists_opens.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_forall_exists_opens.AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_forall_exists_opens.AlgebraicGeometry in
theorem solution {X : Scheme.{u}} {n : ℕ} {M : X.Modules}
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pullback U.ι).obj M)) :
    Scheme.Modules.IsLocallyFreeOfRank n M := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hxU, hU⟩ := h x
  obtain ⟨V, hxV, ⟨e⟩⟩ := hU.exists_trivialization ⟨x, hxU⟩
  refine ⟨U.ι ''ᵁ V, ⟨⟨x, hxU⟩, hxV, rfl⟩, ⟨?_⟩⟩
  let i := U.ι.isoImage V
  have hi : i.inv ≫ V.ι ≫ U.ι = (U.ι ''ᵁ V).ι := U.ι.isoImage_inv_ι V
  exact (pullbackCongr hi.symm).app M ≪≫
    ((pullbackComp i.inv (V.ι ≫ U.ι)).symm.app M) ≪≫
    (Scheme.Modules.pullback i.inv).mapIso
      (((pullbackComp V.ι U.ι).symm.app M) ≪≫ (Scheme.Modules.pullback V.ι).mapIso (Iso.refl _) ≪≫ e) ≪≫
    pullbackFreeIso' i.inv _
