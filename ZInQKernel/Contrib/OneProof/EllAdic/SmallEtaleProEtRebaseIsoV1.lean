import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import ZInQKernel.Contrib.OneProof.EllAdic.SmallEtaleToProEtSiteV1

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

namespace RC53.EllAdic

universe u

local instance rebaseIsoEtaleIdentities :
    MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
  (inferInstance : MorphismProperty.IsMultiplicative (@Etale : MorphismProperty Scheme.{u})).toContainsIdentities

local instance rebaseIsoEtaleComposition :
    MorphismProperty.IsStableUnderComposition (@Etale : MorphismProperty Scheme.{u}) :=
  (inferInstance : MorphismProperty.IsMultiplicative (@Etale : MorphismProperty Scheme.{u})).toIsStableUnderComposition

local instance rebaseIsoWeaklyEtaleIdentities :
    MorphismProperty.ContainsIdentities (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
  (inferInstance : MorphismProperty.IsMultiplicative (@WeaklyEtale : MorphismProperty Scheme.{u})).toContainsIdentities

local instance rebaseIsoWeaklyEtaleComposition :
    MorphismProperty.IsStableUnderComposition (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
  (inferInstance : MorphismProperty.IsMultiplicative (@WeaklyEtale : MorphismProperty Scheme.{u})).toIsStableUnderComposition

/-- Relabel a small étale object by postcomposing with the given base
isomorphism. This keeps its underlying scheme and morphisms unchanged. -/
def smallEtaleRebaseIso {S T : Scheme.{u}} (σ : S ≅ T) : S.Etale ⥤ T.Etale := by
  let h : Etale σ.hom := inferInstance
  exact MorphismProperty.Over.map (P := @Etale) (⊤ : MorphismProperty Scheme.{u}) (f := σ.hom) h

/-- The corresponding relabeling of actual small pro-étale objects. -/
def smallProEtRebaseIso {S T : Scheme.{u}} (σ : S ≅ T) : S.ProEt ⥤ T.ProEt :=
  MorphismProperty.Over.map (⊤ : MorphismProperty Scheme.{u})
    (MorphismProperty.of_isIso (@WeaklyEtale : MorphismProperty Scheme.{u}) σ.hom)

/-- Inclusion and change along the actual scheme isomorphism have the same
underlying slice functor on both routes. -/
theorem smallEtaleToProEt_rebaseIso {S T : Scheme.{u}} (σ : S ≅ T) :
    smallEtaleToProEt S ⋙ smallProEtRebaseIso σ =
      smallEtaleRebaseIso σ ⋙ smallEtaleToProEt T := rfl

/-- The relabeling does not change the argument of the continuous-map
presheaf (the underlying scheme), on either objects or arrows. -/
theorem smallProEtRebaseIso_forget {S T : Scheme.{u}} (σ : S ≅ T) :
    (smallProEtRebaseIso σ ⋙ Scheme.ProEt.forget T) ⋙ Over.forget T =
      Scheme.ProEt.forget S ⋙ Over.forget S := rfl

end RC53.EllAdic
