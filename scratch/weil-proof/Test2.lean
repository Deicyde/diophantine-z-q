import ZInQKernel.Contrib.OneProof.PicDictionary
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MonoidalCategory Limits
universe u
variable {X Y Z : Scheme.{u}}

abbrev PQ (f : X ⟶ Y) := PresheafOfModules.pullback f.toRingCatSheafHom.hom

def pcQ (f : X ⟶ Y) (g : Y ⟶ Z) : PQ g ⋙ PQ f ≅ PQ (f ≫ g) :=
  PresheafOfModules.pullbackComp _ _

example (f : X ⟶ Y) : PQ f = PresheafOfModules.pullbackOfCommRingCat (F := TopologicalSpace.Opens.map f.base)
    (R := X.sheaf.obj) (S := Y.sheaf.obj) f.toRingCatPresheafHom := rfl
