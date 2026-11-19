/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

New actual equality and iterated-pullback primitives for the GIVEN-line
adapter. All scheme/coefficient maps are retained. These are used to prove
that generic conjugation cancels on the actual diagonal, without Picard
uniqueness/cube/unknown hdescLine hypotheses. No generic line extension or
model existence is constructed by these primitives.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineGeneric
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineTwoOpen

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.Pseudofunctor
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent

/-- Literal equality of coefficient maps induces the canonical actual iso. -/
def coefficientEqIso {X T : Scheme.{u}}
    (M : modulesPseudofunctor.obj (.mk (op X))) {x y : T ⟶ X} (h : x = y) :
    (modulesPseudofunctor.map x.op.toLoc).toFunctor.obj M ≅
      (modulesPseudofunctor.map y.op.toLoc).toFunctor.obj M :=
  eqToIso (by cases h; rfl)

theorem coefficientEqIso_pullHom {X T T' : Scheme.{u}}
    (M : modulesPseudofunctor.obj (.mk (op X))) {x y : T ⟶ X} (h : x = y)
    (a : T' ⟶ T) (x' y' : T' ⟶ X) (hx : a ≫ x = x') (hy : a ≫ y = y') :
    pullHom (coefficientEqIso M h).hom a x' y' hx hy =
      (coefficientEqIso M (hx.symm.trans ((congrArg (a ≫ ·) h).trans hy))).hom := by
  cases h
  have he : x' = y' := hx.symm.trans hy
  cases he
  simp only [coefficientEqIso, eqToIso_refl, Iso.refl_hom, pullHom_id_eq_id]

/-- On the ACTUAL diagonal, equal generic lifts make conjugation cancel.
The result is the canonical equality iso, not an arbitrary generic scalar. -/
theorem genericLineCompare_equal {X Xg A T : Scheme.{u}}
    (i : Xg ⟶ X) (q : Xg ⟶ A)
    (M : modulesPseudofunctor.obj (.mk (op X)))
    (L : modulesPseudofunctor.obj (.mk (op A)))
    (β : (modulesPseudofunctor.map i.op.toLoc).toFunctor.obj M ≅
      (modulesPseudofunctor.map q.op.toLoc).toFunctor.obj L)
    (a b : T ⟶ Xg) (x y : T ⟶ X) (z : T ⟶ A)
    (hx : a ≫ i = x) (hy : b ≫ i = y) (ha : a ≫ q = z) (hb : b ≫ q = z)
    (hab : a = b) :
    (genericLineCompare i q M L β a b x y z hx hy ha hb).hom =
      (coefficientEqIso M (hx.symm.trans ((congrArg (· ≫ i) hab).trans hy))).hom := by
  cases hab
  have hxy : x = y := hx.symm.trans hy
  cases hxy
  simp [genericLineCompare, coefficientEqIso]

/-- Put an ACTUAL direct-composite line iso into the two iterated pullbacks.
This is solely the source's real pseudofunctor comparison; all maps are fixed. -/
def iteratedLineIso {X T U : Scheme.{u}}
    (M : modulesPseudofunctor.obj (.mk (op X))) (x y : T ⟶ X) (j : U ⟶ T)
    (E : (modulesPseudofunctor.map (j ≫ x).op.toLoc).toFunctor.obj M ≅
      (modulesPseudofunctor.map (j ≫ y).op.toLoc).toFunctor.obj M) :
    (modulesPseudofunctor.map j.op.toLoc).toFunctor.obj
        ((modulesPseudofunctor.map x.op.toLoc).toFunctor.obj M) ≅
      (modulesPseudofunctor.map j.op.toLoc).toFunctor.obj
        ((modulesPseudofunctor.map y.op.toLoc).toFunctor.obj M) := by
  let φ := pullHomMapComp' E.hom x y (𝟙 U) j j (by simp) (by simp)
  haveI : IsIso φ := by
    dsimp only [φ, pullHomMapComp']
    infer_instance
  exact asIso φ

@[simp]
theorem iteratedLineIso_hom {X T U : Scheme.{u}}
    (M : modulesPseudofunctor.obj (.mk (op X))) (x y : T ⟶ X) (j : U ⟶ T)
    (E : (modulesPseudofunctor.map (j ≫ x).op.toLoc).toFunctor.obj M ≅
      (modulesPseudofunctor.map (j ≫ y).op.toLoc).toFunctor.obj M) :
    (iteratedLineIso M x y j E).hom =
      pullHomMapComp' E.hom x y (𝟙 U) j j (by simp) (by simp) := rfl

/-- Pullback of this actual comparison retains exactly the common test map. -/
theorem iteratedLineIso_pullHom {X T U T' : Scheme.{u}}
    (M : modulesPseudofunctor.obj (.mk (op X))) (x y : T ⟶ X) (j : U ⟶ T)
    (E : (modulesPseudofunctor.map (j ≫ x).op.toLoc).toFunctor.obj M ≅
      (modulesPseudofunctor.map (j ≫ y).op.toLoc).toFunctor.obj M)
    (a : T' ⟶ U) (r : T' ⟶ T) (har : a ≫ j = r) :
    pullHom (iteratedLineIso M x y j E).hom a r r har har =
      pullHomMapComp' E.hom x y a r r
        (by rw [← har, Category.assoc]) (by rw [← har, Category.assoc]) := by
  rw [iteratedLineIso_hom]
  exact pullHom_pullHomMapComp' E.hom x y (𝟙 U) j j (by simp) (by simp)
    a r r har har a (by simp) (by rw [← har, Category.assoc])
    (by rw [← har, Category.assoc])

#print axioms coefficientEqIso_pullHom
#print axioms genericLineCompare_equal
#print axioms iteratedLineIso_pullHom

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
