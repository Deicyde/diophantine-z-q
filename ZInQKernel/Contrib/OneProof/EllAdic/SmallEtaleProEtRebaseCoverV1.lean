import ZInQKernel.Contrib.OneProof.EllAdic.SmallEtaleProEtRebaseIsoV1

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace RC53.EllAdic

universe u

local instance rebaseCoverEtaleComposition :
    MorphismProperty.IsStableUnderComposition (@Etale : MorphismProperty Scheme.{u}) :=
  (inferInstance : MorphismProperty.IsMultiplicative (@Etale : MorphismProperty Scheme.{u})).toIsStableUnderComposition

local instance rebaseCoverWeaklyEtaleComposition :
    MorphismProperty.IsStableUnderComposition (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
  (inferInstance : MorphismProperty.IsMultiplicative (@WeaklyEtale : MorphismProperty Scheme.{u})).toIsStableUnderComposition

local instance rebaseCoverEtaleRespectsIso :
    MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso (P := @Etale)

/-- The small étale relabeling, like the pro-étale relabeling, leaves the
underlying scheme and maps unchanged. -/
theorem smallEtaleRebaseIso_forget {S T : Scheme.{u}} (σ : S ≅ T) :
    (smallEtaleRebaseIso σ ⋙ Scheme.Etale.forget T) ⋙ Over.forget T =
      Scheme.Etale.forget S ⋙ Over.forget S := rfl

private def rebaseEquivalence {S T : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative] [P.RespectsIso] (σ : S ≅ T) :
    P.Over ⊤ S ≌ P.Over ⊤ T := by
  let h : P σ.hom := P.of_isIso σ.hom
  let k : P σ.inv := P.of_isIso σ.inv
  let Q : MorphismProperty Scheme.{u} := ⊤
  refine CategoryTheory.Equivalence.mk (MorphismProperty.Over.map Q h)
    (MorphismProperty.Over.map Q k) ?_ ?_
  · exact (MorphismProperty.Over.mapId (P := P) Q S).symm ≪≫
      MorphismProperty.Over.mapComp Q h k (𝟙 S) σ.hom_inv_id.symm
  · exact (MorphismProperty.Over.mapComp Q k h (𝟙 T) σ.inv_hom_id.symm).symm ≪≫
      MorphismProperty.Over.mapId (P := P) Q T

/-- An equivalence of the actual small étale slice categories, with inverse
postcomposition by the inverse base isomorphism. -/
def smallEtaleRebaseEquivalence {S T : Scheme.{u}} (σ : S ≅ T) : S.Etale ≌ T.Etale :=
  rebaseEquivalence (@Etale : MorphismProperty Scheme.{u}) σ

/-- An equivalence of the actual small pro-étale slice categories. -/
def smallProEtRebaseEquivalence {S T : Scheme.{u}} (σ : S ≅ T) : S.ProEt ≌ T.ProEt :=
  rebaseEquivalence (@WeaklyEtale : MorphismProperty Scheme.{u}) σ

private theorem mem_smallEtale_of_forget (S : Scheme.{u}) {U : S.Etale} (R : Sieve U) :
    R ∈ S.smallEtaleTopology U ↔
      R.functorPushforward (Scheme.Etale.forget S ⋙ Over.forget S) ∈
        Scheme.etaleTopology ((Scheme.Etale.forget S ⋙ Over.forget S).obj U) := by
  let : (Scheme.Etale.forget S).LocallyCoverDense (Scheme.etaleTopology.over S) :=
    Scheme.locallyCoverDense_of_le S (P := @Etale) (Q := @Etale) le_rfl
  change R ∈ (Scheme.Etale.forget S).restrictedTopology (Scheme.etaleTopology.over S) U ↔ _
  rw [Functor.mem_restrictedTopology_iff, GrothendieckTopology.mem_over_iff]
  change ((R.functorPushforward (Scheme.Etale.forget S)).functorPushforward (Over.forget S)) ∈ _ ↔ _
  rw [← Sieve.functorPushforward_comp]
  rfl

private theorem mem_smallProEt_of_forget (S : Scheme.{u}) {U : S.ProEt} (R : Sieve U) :
    R ∈ Scheme.ProEt.topology S U ↔
      R.functorPushforward (Scheme.ProEt.forget S ⋙ Over.forget S) ∈
        Scheme.proetaleTopology ((Scheme.ProEt.forget S ⋙ Over.forget S).obj U) := by
  have hpro : Scheme.ProEt.topology S =
      (Scheme.ProEt.forget S).restrictedTopology (Scheme.proetaleTopology.over S) :=
    MorphismProperty.toGrothendieck_comap_forget_eq_restrictedTopology
      (P := @WeaklyEtale) (S := S) Scheme.proetalePrecoverage
      Scheme.proetalePrecoverage_le_precoverage_weaklyEtale
  rw [hpro, Functor.mem_restrictedTopology_iff, GrothendieckTopology.mem_over_iff]
  change ((R.functorPushforward (Scheme.ProEt.forget S)).functorPushforward (Over.forget S)) ∈ _ ↔ _
  rw [← Sieve.functorPushforward_comp]
  rfl

/-- The literal base-isomorphism functor preserves covers of the small étale site. -/
theorem smallEtaleRebaseIso_coverPreserving {S T : Scheme.{u}} (σ : S ≅ T) :
    CoverPreserving S.smallEtaleTopology T.smallEtaleTopology (smallEtaleRebaseIso σ) := by
  refine ⟨?_⟩
  intro U R hR
  have hs := (mem_smallEtale_of_forget S R).1 hR
  apply (mem_smallEtale_of_forget T _).2
  rw [← Sieve.functorPushforward_comp]
  have h : smallEtaleRebaseIso σ ⋙ (Scheme.Etale.forget T ⋙ Over.forget T) =
      Scheme.Etale.forget S ⋙ Over.forget S := smallEtaleRebaseIso_forget σ
  exact (congrArg (fun F : S.Etale ⥤ Scheme.{u} =>
    R.functorPushforward F ∈ Scheme.etaleTopology (F.obj U)) h).mpr hs

/-- The literal base-isomorphism functor preserves covers of the small pro-étale site. -/
theorem smallProEtRebaseIso_coverPreserving {S T : Scheme.{u}} (σ : S ≅ T) :
    CoverPreserving (Scheme.ProEt.topology S) (Scheme.ProEt.topology T) (smallProEtRebaseIso σ) := by
  refine ⟨?_⟩
  intro U R hR
  have hs := (mem_smallProEt_of_forget S R).1 hR
  apply (mem_smallProEt_of_forget T _).2
  rw [← Sieve.functorPushforward_comp]
  have h : smallProEtRebaseIso σ ⋙ (Scheme.ProEt.forget T ⋙ Over.forget T) =
      Scheme.ProEt.forget S ⋙ Over.forget S := smallProEtRebaseIso_forget σ
  exact (congrArg (fun F : S.ProEt ⥤ Scheme.{u} =>
    R.functorPushforward F ∈ Scheme.proetaleTopology (F.obj U)) h).mpr hs

instance smallEtaleRebaseIso_isContinuous {S T : Scheme.{u}} (σ : S ≅ T) :
    (smallEtaleRebaseIso σ).IsContinuous S.smallEtaleTopology T.smallEtaleTopology := by
  let : (smallEtaleRebaseIso σ).IsEquivalence :=
    inferInstanceAs (smallEtaleRebaseEquivalence σ).functor.IsEquivalence
  let : RepresentablyFlat (smallEtaleRebaseIso σ) := flat_of_preservesFiniteLimits _
  exact Functor.isContinuous_iff_coverPreserving.2 (smallEtaleRebaseIso_coverPreserving σ)

instance smallProEtRebaseIso_isContinuous {S T : Scheme.{u}} (σ : S ≅ T) :
    (smallProEtRebaseIso σ).IsContinuous (Scheme.ProEt.topology S) (Scheme.ProEt.topology T) := by
  let : (smallProEtRebaseIso σ).IsEquivalence :=
    inferInstanceAs (smallProEtRebaseEquivalence σ).functor.IsEquivalence
  let : RepresentablyFlat (smallProEtRebaseIso σ) := flat_of_preservesFiniteLimits _
  exact Functor.isContinuous_iff_coverPreserving.2 (smallProEtRebaseIso_coverPreserving σ)

end RC53.EllAdic
