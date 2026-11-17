/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NeronModelInfra_isIndexOneExtension_stalk_of_smooth_of_forall_specializes
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_WeakNeronModel
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_NeronModelInfra_isIndexOneExtension_stalk_of_smooth_of_forall_specializes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem NeronModelInfra.isIndexOneExtension_stalk_of_smooth_of_forall_specializes
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z]
    (ζ : Z) (hζ : z.base ζ = IsLocalRing.closedPoint R)
    (hgen : ∀ y : Z, y ⤳ ζ → z.base y = IsLocalRing.closedPoint R → y = ζ)
    [Algebra R (Z.presheaf.stalk ζ)]
    (halg : Z.fromSpecStalk ζ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ζ)))) :
    ∃ (_ : IsDomain (Z.presheaf.stalk ζ)) (_ : IsDiscreteValuationRing (Z.presheaf.stalk ζ))
      (_ : IsLocalHom (algebraMap R (Z.presheaf.stalk ζ))),
      IsIndexOneExtension R (Z.presheaf.stalk ζ) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_isIndexOneExtension_stalk_of_smooth_of_forall_specializes.solution
