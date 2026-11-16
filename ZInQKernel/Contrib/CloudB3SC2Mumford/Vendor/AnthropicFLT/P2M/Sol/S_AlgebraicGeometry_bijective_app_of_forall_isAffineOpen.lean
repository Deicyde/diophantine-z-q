/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_bijective_app_of_forall_isAffineOpen
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_bijective_app_of_forall_isAffineOpen

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

open TopologicalSpace Opposite

namespace SheafGlueGC3

open TopCat TopCat.Presheaf

theorem stalkFunctor_map_surjective_of_isBasis {X : TopCat.{u}} {B : Set (Opens X)} (hB : Opens.IsBasis B)
    {F G : X.Presheaf CommRingCat.{u}} {α : F ⟶ G} (hα : ∀ U ∈ B, Function.Surjective (α.app (op U))) (x : X) :
    Function.Surjective ((stalkFunctor _ x).map α) := by
  intro t
  obtain ⟨U, hxU, hU, t, rfl⟩ := exists_mem_germ_eq_of_isBasis hB G x t
  obtain ⟨s, rfl⟩ := hα U hU t
  exact ⟨F.germ U x hxU s, by rw [stalkFunctor_map_germ_apply]⟩

end SheafGlueGC3

theorem solution {X B : Scheme.{u}} (p : X ⟶ B)
    (h : ∀ U : B.Opens, IsAffineOpen U → Function.Bijective (p.app U)) (U : B.Opens) :
    Function.Bijective (p.app U) := by
  let F : TopCat.Sheaf CommRingCat.{u} B.carrier := B.sheaf
  let G : TopCat.Sheaf CommRingCat.{u} B.carrier := (TopCat.Sheaf.pushforward _ p.base).obj X.sheaf
  let f : F ⟶ G := ⟨p.c⟩
  have key := TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective f U (fun x _ =>
    ⟨TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis B.isBasis_affineOpens
        (fun V hV => (h V hV).1) x,
     SheafGlueGC3.stalkFunctor_map_surjective_of_isBasis B.isBasis_affineOpens
        (fun V hV => (h V hV).2) x⟩)
  exact key
