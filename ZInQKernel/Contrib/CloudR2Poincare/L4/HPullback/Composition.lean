import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Pullback
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Native abelian inverse-image composition and identity

Only the existing W07 inverse-image/constant-sheaf construction and Mathlib
adjunction uniqueness/composition are used. All new declarations are L4-owned;
no upstream source, instance, adjunction or constant-sheaf map is replaced.
-/

noncomputable section
open CategoryTheory Limits TopologicalSpace

namespace ZInQ.Contrib.CloudR2Poincare.L4.HPullback
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section GenericAdjunction
variable {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₀₂ : C₀ ⥤ C₂}
    {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₂₀ : C₂ ⥤ C₀}

/-- The existing constant-sheaf uniqueness construction is the native composition mate. -/
theorem leftAdjointUniq_ofNatIsoRight_comp
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₀₂ : F₀₂ ⊣ G₂₀)
    (e : G₂₁ ⋙ G₁₀ ≅ G₂₀) :
    ((adj₀₁.comp adj₁₂).ofNatIsoRight e).leftAdjointUniq adj₀₂ =
      Adjunction.leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e := by
  ext X
  simp [Adjunction.leftAdjointUniq, Adjunction.leftAdjointCompIso,
    Adjunction.ofNatIsoRight, Adjunction.comp_counit_app]

end GenericAdjunction

open AlgebraicGeometry

/-- The native constant integer sheaf, exactly as in W07's theta declaration. -/
abbrev abelianConstantIntegerSheaf (X : Scheme.{u}) :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))

/-- The whole constant-sheaf functor on the native topological site. -/
abbrev abelianConstantSheafFunctor (X : Scheme.{u}) :=
  constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

/-- Its native evaluation-at-top right adjoint. -/
abbrev abelianSheafSectionsTop (X : Scheme.{u}) :=
  (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (Opposite.op ⊤)

/-- The actual native abelian inverse-image/pushforward adjunction. -/
abbrev abelianInverseImageAdjunction {X Y : Scheme.{u}} (a : X ⟶ Y) :=
  TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} a.base

/-- Native pushforwards compose by literal precomposition on opens. -/
def abelianPushforwardCompIso {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} a.base ⋙
      TopCat.Sheaf.pushforward AddCommGrpCat.{u} b.base ≅
        TopCat.Sheaf.pushforward AddCommGrpCat.{u} (a ≫ b).base :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro M N f
    change (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (a ≫ b).base).map f ≫ 𝟙 _ =
      𝟙 _ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (a ≫ b).base).map f
    simp only [Category.comp_id, Category.id_comp])

/-- The native identity pushforward is the identity functor. -/
def abelianPushforwardIdIso (X : Scheme.{u}) :
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} (𝟙 X : X ⟶ X).base ≅
      𝟭 (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro M N f
    change f ≫ 𝟙 _ = 𝟙 _ ≫ f
    simp only [Category.comp_id, Category.id_comp])

/-- Canonical composition of native abelian inverse-image functors, by adjunction mates. -/
def abelianInverseImageCompIso {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
    Scheme.Modules.abelianInverseImage b ⋙ Scheme.Modules.abelianInverseImage a ≅
      Scheme.Modules.abelianInverseImage (a ≫ b) :=
  Adjunction.leftAdjointCompIso (abelianInverseImageAdjunction b)
    (abelianInverseImageAdjunction a) (abelianInverseImageAdjunction (a ≫ b))
    (abelianPushforwardCompIso a b)

/-- Canonical identity inverse-image isomorphism, by its native adjunction. -/
def abelianInverseImageIdIso (X : Scheme.{u}) :
    Scheme.Modules.abelianInverseImage (𝟙 X) ≅
      𝟭 (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  Adjunction.leftAdjointIdIso (abelianInverseImageAdjunction (𝟙 X))
    (abelianPushforwardIdIso X)

/-- The evident evaluation-at-top compatibility used by W07's constant-sheaf theta. -/
def abelianPushforwardSectionsTopIso {X Y : Scheme.{u}} (a : X ⟶ Y) :
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} a.base ⋙ abelianSheafSectionsTop Y ≅
      abelianSheafSectionsTop X :=
  (Opens.map a.base).sheafPushforwardContinuousCompSheafSectionsObjIso
    AddCommGrpCat.{u} (Opens.grothendieckTopology Y)
    (Opens.grothendieckTopology X) (Opposite.op ⊤)

/-- The actual W07 constant-sheaf functor comparison, before applying it to integers. -/
abbrev abelianInverseImageConstantFunctorIso {X Y : Scheme.{u}} (a : X ⟶ Y) :
    abelianConstantSheafFunctor Y ⋙ Scheme.Modules.abelianInverseImage a ≅
      abelianConstantSheafFunctor X :=
  (Opens.map a.base).constantSheafsheafPullbackIso AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
    isTerminalTop isTerminalTop

/-- W07's theta is literally the mate-based native composition isomorphism. -/
theorem abelianInverseImageConstantFunctorIso_eq_comp {X Y : Scheme.{u}} (a : X ⟶ Y) :
    abelianInverseImageConstantFunctorIso a =
      Adjunction.leftAdjointCompIso
        (constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u} isTerminalTop)
        (abelianInverseImageAdjunction a)
        (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop)
        (abelianPushforwardSectionsTopIso a) := by
  exact leftAdjointUniq_ofNatIsoRight_comp _ _ _ _

end ZInQ.Contrib.CloudR2Poincare.L4.HPullback
