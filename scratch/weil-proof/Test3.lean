import ZInQKernel.Contrib.OneProof.PicDictionary
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MonoidalCategory Limits
universe u
variable {X Y Z : Scheme.{u}}

abbrev PF (f : X ⟶ Y) := PresheafOfModules.pushforwardOfCommRingCat (F := TopologicalSpace.Opens.map f.base)
    (R := X.sheaf.obj) (S := Y.sheaf.obj) f.toRingCatPresheafHom

abbrev PFQ (f : X ⟶ Y) := PresheafOfModules.pushforward f.toRingCatSheafHom.hom

example (f : X ⟶ Y) : PF f = PFQ f := rfl

def eQ (f : X ⟶ Y) (g : Y ⟶ Z) : PFQ f ⋙ PFQ g ≅ PFQ (f ≫ g) := PresheafOfModules.pushforwardComp _ _

def eF (f : X ⟶ Y) (g : Y ⟶ Z) : PF f ⋙ PF g ≅ PF (f ≫ g) := eQ f g

example (f : X ⟶ Y) : (PF f).LaxMonoidal := inferInstance
