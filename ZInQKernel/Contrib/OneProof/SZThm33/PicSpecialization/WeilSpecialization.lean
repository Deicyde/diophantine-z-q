import ZInQKernel.Contrib.OneProof.PicDictionary

noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace PicDict.Transport

variable {X Y : Scheme.{0}}

/-- Comparison for a commuting square with source and target schemes allowed to differ. -/
def pullbackSquareIso (g : Y ⟶ X) (m' : Y ⟶ Y) (m : X ⟶ X)
    (h : g ≫ m = m' ≫ g) (M : X.Modules) :
    (pullback g).obj ((pullback m).obj M) ≅ (pullback m').obj ((pullback g).obj M) :=
  (pullbackComp g m).app M ≪≫ (pullbackCongr h).app M ≪≫ ((pullbackComp m' g).app M).symm

private def translationSquareIso (t' : Y ⟶ Y) (g : Y ⟶ X) (t : X ⟶ X)
    (h : t' ≫ g = g ≫ t) : pullback g ⋙ pullback t' ≅ pullback t ⋙ pullback g :=
  pullbackComp t' g ≪≫ pullbackCongr h ≪≫ (pullbackComp g t).symm

private theorem translationSquareIso_unit (t' : Y ⟶ Y) (g : Y ⟶ X) (t : X ⟶ X)
    (h : t' ≫ g = g ≫ t) :
    (pOU t').inv ≫ (pullback t').map (pOU g).inv ≫
        (translationSquareIso t' g t h).hom.app (unit X) =
      (pOU g).inv ≫ (pullback g).map (pOU t).inv := by
  simp only [translationSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [← reassoc_of% (pOU_inv_comp t' g), reassoc_of% (pOU_inv_congr h), pOU_inv_comp g t]
  simp

private theorem translationSquareIso_pullbackSquareIso (t' m' : Y ⟶ Y) (g : Y ⟶ X)
    (t m : X ⟶ X) (ht : t' ≫ g = g ≫ t) (hm : g ≫ m = m' ≫ g)
    (h : t ≫ m = m) (h' : t' ≫ m' = m') (M : X.Modules) :
    (translationSquareIso t' g t ht).inv.app ((pullback m).obj M) ≫
        (pullback t').map (pullbackSquareIso g m' m hm M).hom ≫
          (pullbackComp t' m').hom.app ((pullback g).obj M) ≫
            (pullbackCongr h').hom.app ((pullback g).obj M) ≫
              (pullbackSquareIso g m' m hm M).inv =
      (pullback g).map ((pullbackComp t m).hom.app M ≫ (pullbackCongr h).hom.app M) := by
  rw [← cancel_mono ((pullbackComp g m).hom.app M)]
  simp only [translationSquareIso, pullbackSquareIso, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv, NatTrans.comp_app, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id, pullbackCongr_hom_app, pullbackCongr_inv_app]
  rw [map_eqToHom_comp_pullbackComp g h M, reassoc_of% (pullbackComp_assoc_app g t m M)]
  rw [reassoc_of% (eqToHom_comp_pullbackComp h' g M)]
  rw [reassoc_of% (pullbackComp_assoc_inv₁ t' m' g M)]
  rw [reassoc_of% (map_eqToHom_comp_pullbackComp t' hm M)]
  rw [reassoc_of% (pullbackComp_assoc_inv₂ t' g m M)]
  rw [reassoc_of% (eqToHom_comp_pullbackComp ht.symm m M)]
  simp

/-- Pull back the trivialization used in the Weil formula along a commuting square. -/
def restrictTriv (g : Y ⟶ X) (m' : Y ⟶ Y) (m : X ⟶ X) (h : g ≫ m = m' ≫ g)
    (M : X.Modules) (ψ : unit X ≅ (pullback m).obj M) :
    unit Y ≅ (pullback m').obj ((pullback g).obj M) :=
  (pOU g).symm ≪≫ (pullback g).mapIso ψ ≪≫ pullbackSquareIso g m' m h M

/-- The Weil formula commutes with restriction to a fibre, including for a
relative trivialization of the multiplication pullback. -/
theorem wf_restrict (t' m' : Y ⟶ Y) (g : Y ⟶ X) (t m : X ⟶ X)
    (ht : t' ≫ g = g ≫ t) (hm : g ≫ m = m' ≫ g)
    (h : t ≫ m = m) (h' : t' ≫ m' = m') (M : X.Modules)
    (ψ : unit X ≅ (pullback m).obj M) :
    wf t' m' h' ((pullback g).obj M) (restrictTriv g m' m hm M ψ) =
      g.appTop (wf t m h M ψ) := by
  simp only [wf, unitHomAddEquiv_apply]
  rw [← pOU_conj g]
  congr 2
  have nat := (translationSquareIso t' g t ht).hom.naturality ψ.hom
  have hmap : (pullback t').map ((pullback g).map ψ.hom) =
      (translationSquareIso t' g t ht).hom.app _ ≫
        (pullback g).map ((pullback t).map ψ.hom) ≫
          (translationSquareIso t' g t ht).inv.app _ := by
    simp only [Functor.comp_map] at nat
    rw [← Category.assoc, ← nat]
    simp
  simp only [restrictTriv, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  rw [hmap]
  simp only [Category.assoc]
  rw [reassoc_of% (translationSquareIso_unit t' g t ht)]
  have hcomp := translationSquareIso_pullbackSquareIso t' m' g t m ht hm h h' M
  simp only [Functor.map_comp] at hcomp
  rw [reassoc_of% hcomp]

end PicDict.Transport
