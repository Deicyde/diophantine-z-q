/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NeronModelInfra_exists_hom_isIso_smoothnessDefect_add_one_le_of_smooth_pullback_snd
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_WeakNeronModel
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_SmoothnessDefect
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_NeronModelInfra_exists_hom_isIso_smoothnessDefect_add_one_le_of_smooth_pullback_snd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

attribute [-simp] AffineDilatation.coe_divElem

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem NeronModelInfra.exists_hom_isIso_smoothnessDefect_add_one_le_of_smooth_pullback_snd
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [QuasiCompact f]
    (hK : Smooth (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃ (X₁ : Scheme.{u}) (v : X₁ ⟶ X),
      IsSeparated v ∧ LocallyOfFiniteType (v ≫ f) ∧ QuasiCompact (v ≫ f) ∧
      IsIso (pullback.map (v ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K) v
        (𝟙 _) (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)) ∧
      IsIso (v ∣_ f.smoothLocus) ∧
      (∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
        [IsLocalHom (algebraMap R R')], IsIndexOneExtension R R' →
        ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f,
          ∃ x₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (v ≫ f),
            x₁.1 ≫ v = x.1) ∧
      (∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
        [IsLocalHom (algebraMap R R')], IsIndexOneExtension R R' →
        ∀ x₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (v ≫ f),
          smoothnessDefect (v ≫ f) x₁.1 + 1 ≤ max 1 (smoothnessDefect f (x₁.1 ≫ v))) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_exists_hom_isIso_smoothnessDefect_add_one_le_of_smooth_pullback_snd.solution
