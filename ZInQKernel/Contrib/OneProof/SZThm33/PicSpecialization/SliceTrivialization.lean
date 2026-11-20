import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.WeilEvaluation

noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace PicDict.Transport

variable {X Y Z P : Scheme.{0}}

/-- Pull a chosen frame back to another scheme. -/
def pullFrame (f : X ⟶ Y) {M : Y.Modules} (e : unit Y ≅ M) :
    unit X ≅ (pullback f).obj M :=
  (pOU f).symm ≪≫ (pullback f).mapIso e

theorem pullFrame_comp (g : X ⟶ Y) (f : Y ⟶ Z) {M : Z.Modules} (e : unit Z ≅ M) :
    pullFrame g (pullFrame f e) ≪≫ (pullbackComp g f).app M = pullFrame (g ≫ f) e := by
  apply Iso.ext
  simp only [pullFrame, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [pOU_inv_comp]
  simp only [Category.assoc]
  have hn := (pullbackComp g f).hom.naturality e.hom
  simp only [Functor.comp_map] at hn
  rw [hn]

/-- Express the pullback of an isomorphism between two pullbacks as an
isomorphism between the corresponding composite pullbacks. -/
def pullIsoAlong (a : X ⟶ P) (l r : P ⟶ P) (M : P.Modules)
    (J : (pullback l).obj M ≅ (pullback r).obj M) :
    (pullback (a ≫ l)).obj M ≅ (pullback (a ≫ r)).obj M :=
  ((pullbackComp a l).app M).symm ≪≫ (pullback a).mapIso J ≪≫ (pullbackComp a r).app M

/-- On a torsion slice, one multiplication comparison supplies an actual
trivialization of the other multiplication pullback. -/
def sliceComparisonTriv (m : X ⟶ X) (a b : X ⟶ P) (l r : P ⟶ P)
    (hm : m ≫ a = a ≫ l) (hb : a ≫ r = b) (M : P.Modules)
    (J : (pullback l).obj M ≅ (pullback r).obj M)
    (e : unit X ≅ (pullback b).obj M) :
    unit X ≅ (pullback m).obj ((pullback a).obj M) :=
  e ≪≫ (pullbackCongr hb.symm).app M ≪≫ (pullIsoAlong a l r M J).symm ≪≫
    (pullbackCongr hm.symm).app M ≪≫ ((pullbackComp m a).app M).symm

theorem pullbackComp_assoc_iso (g : X ⟶ Y) (a : Y ⟶ Z) (l : Z ⟶ P) (M : P.Modules) :
    (pullback g).mapIso ((pullbackComp a l).app M) ≪≫ (pullbackComp g (a ≫ l)).app M =
      (pullbackComp g a).app ((pullback l).obj M) ≪≫ (pullbackComp (g ≫ a) l).app M ≪≫
        (pullbackCongr (Category.assoc g a l)).app M := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, pullbackCongr_hom_app]
  exact pullbackComp_assoc_app g a l M

theorem pullbackCongr_second_iso (g : X ⟶ Y) {a b : Y ⟶ Z} (h : a = b) (M : Z.Modules) :
    (pullback g).mapIso ((pullbackCongr h).app M) ≪≫ (pullbackComp g b).app M =
      (pullbackComp g a).app M ≪≫ (pullbackCongr (congrArg (g ≫ ·) h)).app M := by
  subst h
  apply Iso.ext
  simp [pullbackCongr]

/-- Composition coherence of the comparison between the two pullbacks. -/
theorem pullIsoAlong_comp (g : X ⟶ Y) (a : Y ⟶ P) (l r : P ⟶ P) (M : P.Modules)
    (J : (pullback l).obj M ≅ (pullback r).obj M) :
    ((pullbackComp g (a ≫ l)).app M).symm ≪≫ (pullback g).mapIso (pullIsoAlong a l r M J) ≪≫
        (pullbackComp g (a ≫ r)).app M =
      (pullbackCongr (Category.assoc g a l).symm).app M ≪≫
        pullIsoAlong (g ≫ a) l r M J ≪≫ (pullbackCongr (Category.assoc g a r)).app M := by
  apply Iso.ext
  simp only [pullIsoAlong, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  have hl := congrArg Iso.inv (pullbackComp_assoc_iso g a l M)
  simp only [Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv, pullbackCongr_inv_app,
    Category.assoc] at hl
  rw [reassoc_of% hl]
  have hn := (pullbackComp g a).hom.naturality J.hom
  simp only [Functor.comp_map] at hn
  rw [pullbackComp_assoc_app g a r M, reassoc_of% hn]
  simp only [pullbackCongr_hom_app, Iso.inv_hom_id_app_assoc]

/-- Evaluation of the slice trivialization is obtained by evaluating the
comparison on the slice point, using its multiplication identification. -/
theorem evalTriv_sliceComparison (g : Y ⟶ X) (m : X ⟶ X) (a b : X ⟶ P) (l r : P ⟶ P)
    (hm : m ≫ a = a ≫ l) (hb : a ≫ r = b) (M : P.Modules)
    (J : (pullback l).obj M ≅ (pullback r).obj M)
    (e : unit X ≅ (pullback b).obj M) :
    evalTriv g m ((pullback a).obj M) (sliceComparisonTriv m a b l r hm hb M J e) ≪≫
      (pullbackComp (g ≫ m) a).app M =
    pullFrame g e ≪≫ (pullbackComp g b).app M ≪≫
      (pullbackCongr (show g ≫ b = (g ≫ a) ≫ r by rw [Category.assoc, hb])).app M ≪≫
      (pullIsoAlong (g ≫ a) l r M J).symm ≪≫
      (pullbackCongr (show (g ≫ a) ≫ l = (g ≫ m) ≫ a by rw [Category.assoc, Category.assoc, hm])).app M := by
  apply Iso.ext
  simp only [evalTriv, sliceComparisonTriv, pullFrame, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Functor.mapIso_hom, Functor.map_comp, Category.assoc, pullbackCongr_hom_app]
  rw [pullbackComp_assoc_inv₁ g m a M, reassoc_of% (map_eqToHom_comp_pullbackComp g hm.symm M)]
  have hJ := congrArg Iso.inv (pullIsoAlong_comp g a l r M J)
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.app_inv, Iso.app_hom, Functor.mapIso_inv,
    Category.assoc, pullbackCongr_inv_app] at hJ
  have hswap := congrArg (((pullbackComp g (a ≫ r)).hom.app M) ≫ ·) hJ
  simp only [Iso.hom_inv_id_app_assoc] at hswap
  rw [reassoc_of% hswap, reassoc_of% (map_eqToHom_comp_pullbackComp g hb.symm M)]
  simp

end PicDict.Transport
