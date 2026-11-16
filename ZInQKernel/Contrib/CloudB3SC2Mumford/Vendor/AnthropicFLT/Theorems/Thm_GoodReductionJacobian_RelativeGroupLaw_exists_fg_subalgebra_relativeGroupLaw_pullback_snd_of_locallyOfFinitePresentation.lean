/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

attribute [-instance] AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op
attribute [-simp] AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans

set_option autoImplicit false

-- [port] was: p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType~exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation NeronModelInfra GoodReductionJacobian"
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry hiding exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀))
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFinitePresentation f]
    (L : RelativeGroupLaw A (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))))
    (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ (Lₜ : RelativeGroupLaw ↥T (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))))
        (c : pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
          pullback (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))))
            (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))))
        (_ : IsIso c)
        (hc : c ≫ pullback.snd _ _ = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))
        (_ : c ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
          pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))),
        (∀ {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of A))
            (x y : SchemeHomOver t (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))),
          (L.mul t x y).1 ≫ c =
            ((Lₜ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ↥T A)))).mul t
              ⟨x.1 ≫ c, by rw [Category.assoc, hc, x.2]⟩ ⟨y.1 ≫ c, by rw [Category.assoc, hc, y.2]⟩).1) ∧
(L.IsCommutative → Lₜ.IsCommutative) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation.solution
