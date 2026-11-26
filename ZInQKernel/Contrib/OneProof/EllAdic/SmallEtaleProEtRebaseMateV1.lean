import ZInQKernel.Contrib.OneProof.EllAdic.SmallEtaleProEtRebaseCoverV1
import ZInQKernel.Contrib.OneProof.EllAdic.SmallEtaleAbPullbackV1

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace RC53.EllAdic

universe u

private noncomputable def sheafRestrictionEquivalence
    {C D : Type*} [Category C] [Category D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (e : C ≌ D) (A : Type*) [Category A]
    [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J] :
    Sheaf K A ≌ Sheaf J A := by
  let R := e.functor.sheafPushforwardContinuous A J K
  let R' := e.inverse.sheafPushforwardContinuous A K J
  let : (𝟭 C : C ⥤ C).IsContinuous J J := inferInstance
  let : (𝟭 D : D ⥤ D).IsContinuous K K := inferInstance
  refine CategoryTheory.Equivalence.mk R R' ?_ ?_
  · exact (Functor.sheafPushforwardContinuousComp' e.counitIso A K J K ≪≫
      Functor.sheafPushforwardContinuousId A K).symm
  · exact Functor.sheafPushforwardContinuousComp' e.unitIso.symm A J K J ≪≫
      Functor.sheafPushforwardContinuousId A J

/-- Pullback on the actual abelian small étale sheaves is restriction along
postcomposition with the given base isomorphism. -/
noncomputable def etaleAbRebasePullback {S T : Scheme.{u}} (σ : S ≅ T) :
    Sheaf T.smallEtaleTopology Ab.{u+1} ⥤ Sheaf S.smallEtaleTopology Ab.{u+1} :=
  (smallEtaleRebaseIso σ).sheafPushforwardContinuous Ab.{u+1} S.smallEtaleTopology T.smallEtaleTopology

/-- The corresponding pullback on actual abelian small pro-étale sheaves. -/
noncomputable def proEtAbRebasePullback {S T : Scheme.{u}} (σ : S ≅ T) :
    Sheaf (Scheme.ProEt.topology T) Ab.{u+1} ⥤ Sheaf (Scheme.ProEt.topology S) Ab.{u+1} :=
  (smallProEtRebaseIso σ).sheafPushforwardContinuous Ab.{u+1}
    (Scheme.ProEt.topology S) (Scheme.ProEt.topology T)

noncomputable def etaleAbRebaseEquivalence {S T : Scheme.{u}} (σ : S ≅ T) :
    Sheaf T.smallEtaleTopology Ab.{u+1} ≌ Sheaf S.smallEtaleTopology Ab.{u+1} := by
  let e := smallEtaleRebaseEquivalence σ
  let : e.functor.IsContinuous S.smallEtaleTopology T.smallEtaleTopology :=
    inferInstanceAs ((smallEtaleRebaseIso σ).IsContinuous S.smallEtaleTopology T.smallEtaleTopology)
  let : e.inverse.IsContinuous T.smallEtaleTopology S.smallEtaleTopology :=
    inferInstanceAs ((smallEtaleRebaseIso σ.symm).IsContinuous T.smallEtaleTopology S.smallEtaleTopology)
  exact sheafRestrictionEquivalence S.smallEtaleTopology T.smallEtaleTopology e Ab.{u+1}

noncomputable def proEtAbRebaseEquivalence {S T : Scheme.{u}} (σ : S ≅ T) :
    Sheaf (Scheme.ProEt.topology T) Ab.{u+1} ≌ Sheaf (Scheme.ProEt.topology S) Ab.{u+1} := by
  let e := smallProEtRebaseEquivalence σ
  let : e.functor.IsContinuous (Scheme.ProEt.topology S) (Scheme.ProEt.topology T) :=
    inferInstanceAs ((smallProEtRebaseIso σ).IsContinuous (Scheme.ProEt.topology S) (Scheme.ProEt.topology T))
  let : e.inverse.IsContinuous (Scheme.ProEt.topology T) (Scheme.ProEt.topology S) :=
    inferInstanceAs ((smallProEtRebaseIso σ.symm).IsContinuous (Scheme.ProEt.topology T) (Scheme.ProEt.topology S))
  exact sheafRestrictionEquivalence (Scheme.ProEt.topology S) (Scheme.ProEt.topology T) e Ab.{u+1}

/-- Both routes restrict along the same composite of site functors. The
comparison acts by the identity on each of the resulting presheaves. -/
noncomputable def rebaseDirectImageSquare {S T : Scheme.{u}} (σ : S ≅ T) :
    proEtAbRebasePullback σ ⋙ smallEtaleAbPushforward S ≅
      smallEtaleAbPushforward T ⋙ etaleAbRebasePullback σ := Iso.refl _

end RC53.EllAdic
