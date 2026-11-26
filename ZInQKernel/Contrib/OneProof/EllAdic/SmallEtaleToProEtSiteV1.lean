import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Proetale

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace RC53.EllAdic

universe u

/-- The inclusion of actual small étale objects into small pro-étale objects.
The underlying object and all arrows in the slice are unchanged. -/
def smallEtaleToProEt (S : Scheme.{u}) : S.Etale ⥤ S.ProEt :=
  MorphismProperty.Over.changeProp S etale_le_weaklyEtale le_rfl

/-- Both arrows into the scheme slice agree, not only on objects. -/
theorem smallEtaleToProEt_forget (S : Scheme.{u}) :
    smallEtaleToProEt S ⋙ Scheme.ProEt.forget S = Scheme.Etale.forget S := rfl

instance smallEtaleToProEt_preservesFiniteLimits (S : Scheme.{u}) :
    PreservesFiniteLimits (smallEtaleToProEt S) := by
  let : PreservesFiniteLimits (smallEtaleToProEt S ⋙ Scheme.ProEt.forget S) :=
    smallEtaleToProEt_forget S ▸ inferInstanceAs (PreservesFiniteLimits (Scheme.Etale.forget S))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (Scheme.ProEt.forget S)

/-- Every covering sieve of the small étale site maps to a covering sieve
of the actual small pro-étale site. -/
theorem smallEtaleToProEt_coverPreserving (S : Scheme.{u}) :
    CoverPreserving S.smallEtaleTopology (Scheme.ProEt.topology S) (smallEtaleToProEt S) := by
  let : MorphismProperty.IsStableUnderComposition (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative (@WeaklyEtale : MorphismProperty Scheme.{u})).toIsStableUnderComposition
  let : MorphismProperty.IsStableUnderComposition (@Etale : MorphismProperty Scheme.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative (@Etale : MorphismProperty Scheme.{u})).toIsStableUnderComposition
  let : (Scheme.Etale.forget S).LocallyCoverDense (Scheme.etaleTopology.over S) :=
    Scheme.locallyCoverDense_of_le S (P := @Etale) (Q := @Etale) le_rfl
  have hpro : Scheme.ProEt.topology S =
      (Scheme.ProEt.forget S).restrictedTopology (Scheme.proetaleTopology.over S) :=
    MorphismProperty.toGrothendieck_comap_forget_eq_restrictedTopology
      (P := @WeaklyEtale) (S := S) Scheme.proetalePrecoverage
      Scheme.proetalePrecoverage_le_precoverage_weaklyEtale
  refine ⟨?_⟩
  intro U T hT
  change T ∈ (Scheme.Etale.forget S).restrictedTopology (Scheme.etaleTopology.over S) U at hT
  rw [Functor.mem_restrictedTopology_iff] at hT
  rw [hpro, Functor.mem_restrictedTopology_iff, ← Sieve.functorPushforward_comp]
  change T.functorPushforward (Scheme.Etale.forget S) ∈
    (Scheme.proetaleTopology.over S) ((Scheme.Etale.forget S).obj U)
  rw [GrothendieckTopology.mem_over_iff] at hT ⊢
  exact Scheme.etaleTopology_le_proetaleTopology _ hT

instance smallEtaleToProEt_isContinuous (S : Scheme.{u}) :
    (smallEtaleToProEt S).IsContinuous S.smallEtaleTopology (Scheme.ProEt.topology S) := by
  let : RepresentablyFlat (smallEtaleToProEt S) := flat_of_preservesFiniteLimits _
  exact Functor.isContinuous_iff_coverPreserving.2 (smallEtaleToProEt_coverPreserving S)

end RC53.EllAdic
