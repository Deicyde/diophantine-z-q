/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Opaque abstract-category overlap calculation. The native Scheme.Modules
consumer supplies its actual functor, maps, M and beta. No cover-effectivity,
line extension, ampleness or NOS premise is introduced. Abstracting the WHOLE
calculation prevents reduction of the native modules pseudofunctor proof fields.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLinePullHom

set_option autoImplicit false
noncomputable section
universe u v u' v'

open CategoryTheory Opposite CategoryTheory.Bicategory
open CategoryTheory.Pseudofunctor
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent.Abstract

variable {C : Type u} [Category.{v} C]
variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

/-- The actual equality of base maps, on the fixed coefficient object. -/
def coefficientEqHom {X T : C} (M : F.obj (.mk (op X)))
    {x y : T ⟶ X} (h : x = y) :
    (F.map x.op.toLoc).toFunctor.obj M ⟶
      (F.map y.op.toLoc).toFunctor.obj M :=
  eqToHom (by cases h; rfl)

theorem coefficientEqHom_pullHom {X T T' : C}
    (M : F.obj (.mk (op X))) {x y : T ⟶ X} (h : x = y)
    (a : T' ⟶ T) (x' y' : T' ⟶ X) (hx : a ≫ x = x') (hy : a ≫ y = y') :
    pullHom (coefficientEqHom M h) a x' y' hx hy =
      coefficientEqHom M (hx.symm.trans ((congrArg (a ≫ ·) h).trans hy)) := by
  cases h
  have he : x' = y' := hx.symm.trans hy
  cases he
  simp only [coefficientEqHom, eqToHom_refl, pullHom_id_eq_id]

/-- Cancellation uses equal ACTUAL lifts, not a prescribed scalar iso. -/
theorem conjugatedCompare_equal {X Xg A T : C}
    (i : Xg ⟶ X) (q : Xg ⟶ A)
    {M : F.obj (.mk (op X))} {L : F.obj (.mk (op A))}
    (β : (F.map i.op.toLoc).toFunctor.obj M ≅ (F.map q.op.toLoc).toFunctor.obj L)
    (a b : T ⟶ Xg) (x y : T ⟶ X) (z : T ⟶ A)
    (hx : a ≫ i = x) (hy : b ≫ i = y) (ha : a ≫ q = z) (hb : b ≫ q = z)
    (hab : a = b) :
    pullHom β.hom a x z hx ha ≫ pullHom β.inv b z y hb hy =
      coefficientEqHom M (hx.symm.trans ((congrArg (· ≫ i) hab).trans hy)) := by
  cases hab
  have hxy : x = y := hx.symm.trans hy
  cases hxy
  rw [← pullHom_comp β.hom β.inv a x z x hx ha hx, β.hom_inv_id]
  simp only [coefficientEqHom, eqToHom_refl, pullHom_id_eq_id]

/-- Naturality of the original comparison from a direct to iterated pullback. -/
theorem iteratedCompare_pullHom {X T U T' : C}
    {M : F.obj (.mk (op X))} (x y : T ⟶ X) (j : U ⟶ T)
    (E : (F.map (j ≫ x).op.toLoc).toFunctor.obj M ⟶
      (F.map (j ≫ y).op.toLoc).toFunctor.obj M)
    (a : T' ⟶ U) (r : T' ⟶ T) (har : a ≫ j = r) :
    pullHom (pullHomMapComp' E x y (𝟙 U) j j (by simp) (by simp))
        a r r har har =
      pullHomMapComp' E x y a r r
        (by rw [← har, Category.assoc]) (by rw [← har, Category.assoc]) := by
  exact pullHom_pullHomMapComp' E x y (𝟙 U) j j (by simp) (by simp)
    a r r har har a (by simp) (by rw [← har, Category.assoc])
    (by rw [← har, Category.assoc])

/-- The complete diagonal/generic overlap equation, with every original map.
Only mono generic inclusion and actual diagonal equality are used. -/
theorem twoMapComparisons_compatible
    {X Xg A T D H T' : C} (i : Xg ⟶ X) [Mono i] (q : Xg ⟶ A)
    {M : F.obj (.mk (op X))} {L : F.obj (.mk (op A))}
    (β : (F.map i.op.toLoc).toFunctor.obj M ≅ (F.map q.op.toLoc).toFunctor.obj L)
    (x y : T ⟶ X) (jD : D ⟶ T) (jH : H ⟶ T)
    (hD : jD ≫ x = jD ≫ y)
    (a b : H ⟶ Xg) (hx : a ≫ i = jH ≫ x) (hy : b ≫ i = jH ≫ y)
    (hq : a ≫ q = b ≫ q)
    (r : T' ⟶ T) (d : T' ⟶ D) (h : T' ⟶ H)
    (hdr : d ≫ jD = r) (hhr : h ≫ jH = r) :
    pullHom (pullHomMapComp' (coefficientEqHom M hD)
          x y (𝟙 D) jD jD (by simp) (by simp)) d r r hdr hdr =
      pullHom (pullHomMapComp'
          (pullHom β.hom a (jH ≫ x) (a ≫ q) hx rfl ≫
            pullHom β.inv b (a ≫ q) (jH ≫ y) hq.symm hy)
          x y (𝟙 H) jH jH (by simp) (by simp)) h r r hhr hhr := by
  have hdx : d ≫ (jD ≫ x) = r ≫ x := by rw [← Category.assoc, hdr]
  have hdy : d ≫ (jD ≫ y) = r ≫ y := by rw [← Category.assoc, hdr]
  have hhx : h ≫ (jH ≫ x) = r ≫ x := by rw [← Category.assoc, hhr]
  have hhy : h ≫ (jH ≫ y) = r ≫ y := by rw [← Category.assoc, hhr]
  have hxy : r ≫ x = r ≫ y := hdx.symm.trans ((congrArg (d ≫ ·) hD).trans hdy)
  have hga : (h ≫ a) ≫ i = r ≫ x := by rw [Category.assoc, hx, hhx]
  have hgb : (h ≫ b) ≫ i = r ≫ y := by rw [Category.assoc, hy, hhy]
  have hab : h ≫ a = h ≫ b := by
    apply (cancel_mono i).mp
    rw [hga, hgb, hxy]
  let z := h ≫ (a ≫ q)
  have haq : (h ≫ a) ≫ q = z := by rw [Category.assoc]
  have hbq : (h ≫ b) ≫ q = z := by rw [Category.assoc, ← hq]
  have hmidD : pullHom (coefficientEqHom M hD) d (r ≫ x) (r ≫ y) hdx hdy =
      coefficientEqHom M hxy :=
    coefficientEqHom_pullHom M hD d (r ≫ x) (r ≫ y) hdx hdy
  have hmidH : pullHom
      (pullHom β.hom a (jH ≫ x) (a ≫ q) hx rfl ≫
        pullHom β.inv b (a ≫ q) (jH ≫ y) hq.symm hy)
        h (r ≫ x) (r ≫ y) hhx hhy = coefficientEqHom M hxy := by
    exact (pullHom_conjugatedComparisons_of_eq i q β a b
      (jH ≫ x) (jH ≫ y) (a ≫ q) hx hy rfl hq.symm h
      (r ≫ x) (r ≫ y) z hhx hhy rfl).trans
        (conjugatedCompare_equal i q β (h ≫ a) (h ≫ b)
          (r ≫ x) (r ≫ y) z hga hgb haq hbq hab)
  rw [iteratedCompare_pullHom x y jD _ d r hdr,
    iteratedCompare_pullHom x y jH _ h r hhr]
  dsimp only [pullHomMapComp']
  rw [hmidD, hmidH]

#print axioms coefficientEqHom_pullHom
#print axioms conjugatedCompare_equal
#print axioms iteratedCompare_pullHom
#print axioms twoMapComparisons_compatible

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent.Abstract
