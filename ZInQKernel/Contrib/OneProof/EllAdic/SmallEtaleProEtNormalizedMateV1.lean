import ZInQKernel.Contrib.OneProof.EllAdic.RebaseAdjunctionMateV1
import ZInQKernel.Contrib.OneProof.EllAdic.SmallEtaleProEtRebaseMateV1

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

namespace RC53.EllAdic

universe u

/-- The specific inverse-image square for postcomposition by `σ.hom`,
normalized by the literal restriction square on the right images. -/
noncomputable def smallEtaleRebaseNormalizedMate {S T : Scheme.{u}} (σ : S ≅ T) :
    etaleAbRebasePullback σ ⋙ smallEtaleAbPullback S ≅
      smallEtaleAbPullback T ⋙ proEtAbRebasePullback σ := by
  letI : (etaleAbRebasePullback σ).IsEquivalence :=
    inferInstanceAs (etaleAbRebaseEquivalence σ).functor.IsEquivalence
  letI : (proEtAbRebasePullback σ).IsEquivalence :=
    inferInstanceAs (proEtAbRebaseEquivalence σ).functor.IsEquivalence
  exact rebaseMateIso (smallEtaleAbAdjunction S) (smallEtaleAbAdjunction T) (rebaseDirectImageSquare σ)

/-- Computing the transpose keeps the actual inverse-image map on the same
sheaves under the restriction-adjunction units. No independently selected
isomorphism of coefficient objects occurs in this formula. -/
theorem smallEtaleRebaseNormalizedMate_transpose {S T : Scheme.{u}} (σ : S ≅ T)
    (X : Sheaf T.smallEtaleTopology Ab.{u+1})
    (Y : Sheaf (Scheme.ProEt.topology T) Ab.{u+1})
    (f : (smallEtaleAbPullback T).obj X ⟶ Y) :
    (smallEtaleAbAdjunction S).homEquiv ((etaleAbRebasePullback σ).obj X)
      ((proEtAbRebasePullback σ).obj Y)
        ((smallEtaleRebaseNormalizedMate σ).hom.app X ≫ (proEtAbRebasePullback σ).map f) =
      (etaleAbRebasePullback σ).map ((smallEtaleAbAdjunction T).homEquiv X Y f) ≫
        (rebaseDirectImageSquare σ).inv.app Y := by
  unfold smallEtaleRebaseNormalizedMate
  rw [rebaseMateIso_hom]
  exact rebaseMateHom_transpose (smallEtaleAbAdjunction S) (smallEtaleAbAdjunction T) (rebaseDirectImageSquare σ) f

end RC53.EllAdic
