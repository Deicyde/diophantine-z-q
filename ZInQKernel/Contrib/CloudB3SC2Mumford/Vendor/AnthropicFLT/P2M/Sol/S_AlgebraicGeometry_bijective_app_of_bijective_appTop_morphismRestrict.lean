/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_bijective_app_of_bijective_appTop_morphismRestrict
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

namespace P2MW.S_AlgebraicGeometry_bijective_app_of_bijective_appTop_morphismRestrict

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

open TopologicalSpace Opposite

namespace P4Aux

theorem bijective_app_congr {X B : Scheme.{u}} (p : X ⟶ B) {V W : B.Opens} (e : V = W)
    (h : Function.Bijective (p.app V)) : Function.Bijective (p.app W) := by
  subst e; exact h

end P4Aux

open P4Aux

set_option backward.isDefEq.respectTransparency false in

theorem solution {X B : Scheme.{u}} (p : X ⟶ B) (U : B.Opens)
    (h : Function.Bijective (p ∣_ U).appTop) : Function.Bijective (p.app U) := by
  have e : U.ι ''ᵁ ⊤ = U := U.ι_image_top
  apply bijective_app_congr p e
  have key : p.app (U.ι ''ᵁ ⊤) =
      (p ∣_ U).appTop ≫ X.presheaf.map (eqToHom (image_morphismRestrict_preimage p U ⊤).symm).op := by
    simp only [morphismRestrict_appTop, Category.assoc, ← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl,
      op_id]
    rw [show X.presheaf.map (𝟙 _) = 𝟙 _ from X.presheaf.map_id _, Category.comp_id]
  rw [key]
  exact (ConcreteCategory.bijective_of_isIso
    (X.presheaf.map (eqToHom (image_morphismRestrict_preimage p U ⊤).symm).op)).comp h
