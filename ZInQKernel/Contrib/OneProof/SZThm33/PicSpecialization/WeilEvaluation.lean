import ZInQKernel.Contrib.OneProof.PicDictionary

noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace PicDict.Transport

variable {X Y : Scheme.{0}}

/-- Pull a trivialization of the multiplication pullback back to a test point. -/
def evalTriv (g : Y ⟶ X) (m : X ⟶ X) (M : X.Modules)
    (ψ : unit X ≅ (pullback m).obj M) :
    unit Y ≅ (pullback (g ≫ m)).obj M :=
  (pOU g).symm ≪≫ (pullback g).mapIso ψ ≪≫ (pullbackComp g m).app M

/-- The pullbacks evaluated before and after translation are along the same
point after multiplying. Compare the two induced trivializations. -/
def evalTrivRatio (g : Y ⟶ X) (t m : X ⟶ X) (h : t ≫ m = m) (M : X.Modules)
    (ψ : unit X ≅ (pullback m).obj M) : unit Y ≅ unit Y :=
  evalTriv (g ≫ t) m M ψ ≪≫ (pullbackCongr (by rw [Category.assoc, h])).app M ≪≫
    (evalTriv g m M ψ).symm

private theorem eval_pullbackComp (g : Y ⟶ X) (t m : X ⟶ X) (h : t ≫ m = m) (M : X.Modules) :
    (pullbackComp g t).hom.app ((pullback m).obj M) ≫
      (pullbackComp (g ≫ t) m).hom.app M ≫
        (pullbackCongr (show (g ≫ t) ≫ m = g ≫ m by rw [Category.assoc, h])).hom.app M ≫
          (pullbackComp g m).inv.app M =
    (pullback g).map ((pullbackComp t m).hom.app M ≫ (pullbackCongr h).hom.app M) := by
  rw [← cancel_mono ((pullbackComp g m).hom.app M)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Functor.map_comp,
    pullbackCongr_hom_app]
  rw [map_eqToHom_comp_pullbackComp g h M, reassoc_of% (pullbackComp_assoc_app g t m M)]
  simp

/-- The Weil formula evaluated at a point compares the trivializations at
that point and at its translate, after identifying their multiplied images. -/
theorem wf_eval (g : Y ⟶ X) (t m : X ⟶ X) (h : t ≫ m = m) (M : X.Modules)
    (ψ : unit X ≅ (pullback m).obj M) :
    g.appTop (wf t m h M ψ) =
      unitHomAddEquiv (unit Y) (evalTrivRatio g t m h M ψ).hom := by
  simp only [wf, unitHomAddEquiv_apply]
  rw [← pOU_conj g]
  congr 2
  have hn := (pullbackComp g t).hom.naturality ψ.hom
  have hs : (pullback (g ≫ t)).map ψ.hom =
      (pullbackComp g t).inv.app (unit X) ≫
        (pullback g).map ((pullback t).map ψ.hom) ≫
          (pullbackComp g t).hom.app ((pullback m).obj M) := by
    simp only [Functor.comp_map] at hn
    rw [hn]
    simp
  simp only [evalTrivRatio, evalTriv, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp,
    Category.assoc]
  rw [hs, pOU_inv_comp, Category.assoc]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% (eval_pullbackComp g t m h M)]
  simp [Functor.map_comp]

end PicDict.Transport
