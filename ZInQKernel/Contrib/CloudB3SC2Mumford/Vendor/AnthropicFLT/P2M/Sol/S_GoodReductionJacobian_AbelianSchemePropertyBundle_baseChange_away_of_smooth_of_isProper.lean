/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_baseChange_away_of_smooth_of_isProper
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_baseChange_away_of_smooth_of_isProper

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (hs : Smooth f) (hp : IsProper f) (hc : ∀ s : Spec (CommRingCat.of R), _root_.IsConnected (f.base ⁻¹' {s}))
    (r : R) (L : RelativeGroupLaw (Localization.Away r)
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))))) :
    AbelianSchemePropertyBundle (Localization.Away r)
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))) := by
  haveI := hs
  haveI := hp
  refine ⟨inferInstance, MorphismProperty.pullback_snd (P := @IsProper) _ _ hp, ?_, ⟨L⟩⟩
  intro s'

  have hinj : Function.Injective
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))).base :=
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))).isOpenEmbedding.injective
  have key : (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))).base ⁻¹' {s'} =
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))).base ⁻¹'
        (f.base ⁻¹' {(Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))).base s'}) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    have hcond := Scheme.Hom.comp_apply (pullback.fst f _) f z
    rw [pullback.condition, Scheme.Hom.comp_apply] at hcond

    constructor
    · intro hz; rw [← hcond, hz]
    · intro hz; exact hinj (hcond.trans hz)
  rw [key]
  refine (hc _).preimage_of_isOpenMap (pullback.fst f _).isOpenEmbedding.injective
    (pullback.fst f _).isOpenEmbedding.isOpenMap ?_
  rw [Scheme.Pullback.range_fst]
  intro a ha
  exact ⟨s', ha.symm⟩
