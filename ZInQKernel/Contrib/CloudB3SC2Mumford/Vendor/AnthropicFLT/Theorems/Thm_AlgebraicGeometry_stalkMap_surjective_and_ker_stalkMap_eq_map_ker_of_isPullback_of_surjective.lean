/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_stalkMap_surjective_and_ker_stalkMap_eq_map_ker_of_isPullback_of_surjective
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_stalkMap_surjective_and_ker_stalkMap_eq_map_ker_of_isPullback_of_surjective

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.stalkMap_surjective_and_ker_stalkMap_eq_map_ker_of_isPullback_of_surjective
    {O κ : Type u} [CommRing O] [CommRing κ] (q : O →+* κ) (hq : Function.Surjective q)
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of O)) (g : Y ⟶ X) (t : Y ⟶ Spec (CommRingCat.of κ))
    (H : IsPullback g t f (Spec.map (CommRingCat.ofHom q))) (y : Y) :
    Function.Surjective (g.stalkMap y).hom ∧
      RingHom.ker (g.stalkMap y).hom =
        Ideal.map ((X.presheaf.germ ⊤ (g.base y) trivial).hom.comp
          ((f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom)) (RingHom.ker q) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_stalkMap_surjective_and_ker_stalkMap_eq_map_ker_of_isPullback_of_surjective.solution
