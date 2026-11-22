import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.ComparisonAxes

noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace PicDict.Transport

variable {X Y Z W P : Scheme.{0}}

/-- Pull a frame of a pulled-back line to the composite test morphism. -/
def pullFramedAlong (f : X ⟶ Y) (i : Y ⟶ P) {M : P.Modules}
    (α : unit Y ≅ (pullback i).obj M) : unit X ≅ (pullback (f ≫ i)).obj M :=
  pullFrame f α ≪≫ (pullbackComp f i).app M

theorem pullFramedAlong_comp (g : Z ⟶ X) (f : X ⟶ Y) (i : Y ⟶ P) {M : P.Modules}
    (α : unit Y ≅ (pullback i).obj M) :
    pullFramedAlong g (f ≫ i) (pullFramedAlong f i α) =
      pullFramedAlong (g ≫ f) i α ≪≫ (pullbackCongr (Category.assoc g f i)).app M := by
  apply Iso.ext
  simp only [pullFramedAlong, pullFrame, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc, pullbackCongr_hom_app]
  rw [pullbackComp_assoc_app g f i M]
  have e := congrArg Iso.hom (pullFrame_comp g f α)
  simp only [pullFrame, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc] at e
  rw [reassoc_of% e]

theorem pullFramedAlong_congr (g : Z ⟶ X) {f f' : X ⟶ P} (h : f = f') {M : P.Modules}
    (α : unit X ≅ (pullback f).obj M) :
    pullFramedAlong g f' (α ≪≫ (pullbackCongr h).app M) =
      pullFramedAlong g f α ≪≫ (pullbackCongr (congrArg (g ≫ ·) h)).app M := by
  subst h
  apply Iso.ext
  simp [pullFramedAlong, pullFrame, pullbackCongr]

/-- Compatible frames on two maps to a line remain compatible after
pullback by any further test morphism. -/
theorem pullFramedAlong_comp_of_agreement (x : W ⟶ Z) (s : Z ⟶ Y) (t : Z ⟶ X)
    (i : Y ⟶ P) (j : X ⟶ P) (h : s ≫ i = t ≫ j) {M : P.Modules}
    (α : unit Y ≅ (pullback i).obj M) (β : unit X ≅ (pullback j).obj M)
    (hα : pullFramedAlong s i α ≪≫ (pullbackCongr h).app M = pullFramedAlong t j β) :
    pullFramedAlong (x ≫ s) i α ≪≫
      (pullbackCongr (show (x ≫ s) ≫ i = (x ≫ t) ≫ j by
        rw [Category.assoc, Category.assoc, h])).app M =
      pullFramedAlong (x ≫ t) j β := by
  have he := congrArg (pullFramedAlong x (t ≫ j)) hα
  rw [pullFramedAlong_congr, pullFramedAlong_comp, pullFramedAlong_comp] at he
  apply Iso.ext
  have he' := congrArg Iso.hom he
  simp only [Iso.trans_hom, Iso.app_hom, pullbackCongr_hom_app, Category.assoc, eqToHom_trans] at he'
  rw [← cancel_mono ((pullbackCongr (Category.assoc x t j)).hom.app M)]
  simp only [Iso.trans_hom, Iso.app_hom, pullbackCongr_hom_app, Category.assoc, eqToHom_trans]
  exact he'

end PicDict.Transport

#print axioms PicDict.Transport.pullFramedAlong_comp_of_agreement
