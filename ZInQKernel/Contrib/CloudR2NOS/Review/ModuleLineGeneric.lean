/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

New GIVEN-line generic compatibility construction. The maps are actual
pullbacks of one GIVEN generic-line iso to the ORIGINAL generic line; identity,
coordinate compatibility and cocycle are proved by those actual maps. No
Picard-class uniqueness, cube, IsMonHom, desired hdescLine or scalar-extension
Fact is supplied. No line on the full model or model existence is constructed
here. This is the generic half of the diagonal/generic module-line adapter.
-/
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.PullbackUnit
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.CategoryTheory.Sites.Descent.PullHom
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLinePullHom

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.Pseudofunctor
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent

variable {X Xg A : Scheme.{u}} (i : Xg ⟶ X) (q : Xg ⟶ A)
  (M : modulesPseudofunctor.obj (.mk (op X)))
  (L : modulesPseudofunctor.obj (.mk (op A)))
  (β : (modulesPseudofunctor.map i.op.toLoc).toFunctor.obj M ≅
    (modulesPseudofunctor.map q.op.toLoc).toFunctor.obj L)

/-- Pull the GIVEN generic identification along the ACTUAL generic point map,
with its original model and original-variety coordinate maps explicit. -/
def pulledLineComparison {T : Scheme.{u}} (a : T ⟶ Xg) (x : T ⟶ X) (z : T ⟶ A)
    (hx : a ≫ i = x) (hz : a ≫ q = z) :
    (modulesPseudofunctor.map x.op.toLoc).toFunctor.obj M ≅
      (modulesPseudofunctor.map z.op.toLoc).toFunctor.obj L where
  hom := pullHom β.hom a x z hx hz
  inv := pullHom β.inv a z x hz hx
  hom_inv_id := by rw [← pullHom_comp, β.hom_inv_id, pullHom_id_eq_id]
  inv_hom_id := by rw [← pullHom_comp, β.inv_hom_id, pullHom_id_eq_id]

/-- Generic transport of the GIVEN line is ACTUAL conjugation through the
SAME original generic-line coordinates, not an assumed descended line class. -/
def genericLineCompare {T : Scheme.{u}} (a b : T ⟶ Xg) (x y : T ⟶ X) (z : T ⟶ A)
    (hx : a ≫ i = x) (hy : b ≫ i = y) (ha : a ≫ q = z) (hb : b ≫ q = z) :
    (modulesPseudofunctor.map x.op.toLoc).toFunctor.obj M ≅
      (modulesPseudofunctor.map y.op.toLoc).toFunctor.obj M :=
  pulledLineComparison i q M L β a x z hx ha ≪≫
    (pulledLineComparison i q M L β b y z hy hb).symm

/-- Opaque projection equation keeps kernel checking of iterated pullback
naturality from unfolding the complete isomorphism's proof fields. -/
@[simp]
theorem genericLineCompare_hom {T : Scheme.{u}} (a b : T ⟶ Xg)
    (x y : T ⟶ X) (z : T ⟶ A)
    (hx : a ≫ i = x) (hy : b ≫ i = y) (ha : a ≫ q = z) (hb : b ≫ q = z) :
    (genericLineCompare i q M L β a b x y z hx hy ha hb).hom =
      pullHom β.hom a x z hx ha ≫ pullHom β.inv b z y hb hy := rfl

/-- Original generic-line coordinates are preserved by the actual iso. -/
theorem genericLineCompare_coordinate {T : Scheme.{u}}
    (a b : T ⟶ Xg) (x y : T ⟶ X) (z : T ⟶ A)
    (hx : a ≫ i = x) (hy : b ≫ i = y) (ha : a ≫ q = z) (hb : b ≫ q = z) :
    (genericLineCompare i q M L β a b x y z hx hy ha hb).hom ≫
        (pulledLineComparison i q M L β b y z hy hb).hom =
      (pulledLineComparison i q M L β a x z hx ha).hom := by
  simp [genericLineCompare, Category.assoc]

/-- Literal identity, with every scheme/field map unchanged. -/
theorem genericLineCompare_self {T : Scheme.{u}} (a : T ⟶ Xg) (x : T ⟶ X) (z : T ⟶ A)
    (hx : a ≫ i = x) (ha : a ≫ q = z) :
    (genericLineCompare i q M L β a a x x z hx hx ha ha).hom = 𝟙 _ := by
  simp [genericLineCompare]

/-- Actual triple cocycle, by cancellation of the SAME middle comparison. -/
theorem genericLineCompare_cocycle {T : Scheme.{u}}
    (a b c : T ⟶ Xg) (x y w : T ⟶ X) (z : T ⟶ A)
    (hx : a ≫ i = x) (hy : b ≫ i = y) (hw : c ≫ i = w)
    (ha : a ≫ q = z) (hb : b ≫ q = z) (hc : c ≫ q = z) :
    (genericLineCompare i q M L β a b x y z hx hy ha hb).hom ≫
        (genericLineCompare i q M L β b c y w z hy hw hb hc).hom =
      (genericLineCompare i q M L β a c x w z hx hw ha hc).hom := by
  simp [genericLineCompare, Category.assoc]

/-- Naturality under ACTUAL further base change, retaining the original
coefficient maps and coherent iterated pullbacks. -/
theorem genericLineCompare_pullHom {T T' : Scheme.{u}}
    (a b : T ⟶ Xg) (x y : T ⟶ X) (z : T ⟶ A)
    (hx : a ≫ i = x) (hy : b ≫ i = y) (ha : a ≫ q = z) (hb : b ≫ q = z)
    (t : T' ⟶ T) :
    pullHom (genericLineCompare i q M L β a b x y z hx hy ha hb).hom t
        (t ≫ x) (t ≫ y) rfl rfl =
      (genericLineCompare i q M L β (t ≫ a) (t ≫ b) (t ≫ x) (t ≫ y) (t ≫ z)
        (by rw [Category.assoc, hx]) (by rw [Category.assoc, hy])
        (by rw [Category.assoc, ha]) (by rw [Category.assoc, hb])).hom := by
  rw [genericLineCompare_hom, genericLineCompare_hom]
  exact pullHom_conjugatedComparisons (F := modulesPseudofunctor) i q β
    a b x y z hx hy ha hb t

#print axioms genericLineCompare_coordinate
#print axioms genericLineCompare_self
#print axioms genericLineCompare_cocycle
#print axioms genericLineCompare_pullHom

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
