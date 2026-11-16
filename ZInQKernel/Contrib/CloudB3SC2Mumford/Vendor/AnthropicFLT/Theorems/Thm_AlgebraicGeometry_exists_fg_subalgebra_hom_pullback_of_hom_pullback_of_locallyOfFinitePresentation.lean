/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

attribute [-instance] AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op
attribute [-simp] AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ Spec (CommRingCat.of A₀)) (f₂ : X₂ ⟶ Spec (CommRingCat.of A₀))
    [QuasiCompact f₁] [QuasiSeparated f₁] [LocallyOfFinitePresentation f₂]
    (g : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
      pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))
    (hg : g ≫ pullback.snd f₂ _ = pullback.snd f₁ _) (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ g₀ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ⟶
          pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))),
        g₀ ≫ pullback.snd f₂ _ = pullback.snd f₁ _ ∧
        ∀ (q₁ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
              pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))))
          (q₂ : pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
              pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))),
          q₁ ≫ pullback.fst f₁ _ = pullback.fst f₁ _ →
          q₁ ≫ pullback.snd f₁ _ = pullback.snd f₁ _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) →
          q₂ ≫ pullback.fst f₂ _ = pullback.fst f₂ _ →
          q₂ ≫ pullback.snd f₂ _ = pullback.snd f₂ _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) →
          q₁ ≫ g₀ = g ≫ q₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation.solution
