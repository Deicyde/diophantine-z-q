/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.Interfaces
import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral

/-!
# Genuine geometric input for W13 dictionary D2

Original dictionary glue, 2026-11-15, W01/Metamate with agentcloud assistance.
The unchanged canonical H5/FLT field-geometric proof supplies its general
04KV algebraic-extension connectedness and smooth-domain-stalk lemmas. We
apply them to the ACTUAL FakeEC source and its OWN relative-law identity,
not a new model, an assumed geometrically integral fibre, or another D lane.
The canonical source imports are read-only; no vendor/provider is duplicated.

Properness/smoothness are the actual bundle fields. Connectedness is the
actual unique fibre over Spec K. The selected section is E.L.one(id), and
we prove integrality of EVERY field-base-change pullback below. Characteristic
zero is unnecessary for this input; the final D2 statement keeps it unchanged.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D2

open CategoryTheory Limits AlgebraicGeometry
open ZInQ.Contrib.CloudW03NeronSurj

/-- The source's actual rational identity section, with its original over equation. -/
def identitySection {K : Type} [Field K] (E : FakeEC K) :
    Spec (CommRingCat.of K) ⟶ E.A :=
  (E.L.one (𝟙 _)).1

@[simp] theorem identitySection_over {K : Type} [Field K] (E : FakeEC K) :
    identitySection E ≫ E.f = 𝟙 _ :=
  (E.L.one (𝟙 _)).2

/-- The bundle's connected actual fibre is the whole source over the unique field point. -/
theorem connectedSpace {K : Type} [Field K] (E : FakeEC K) : ConnectedSpace E.A := by
  rw [connectedSpace_iff_univ]
  have hfibre : E.f.base ⁻¹' {(IsLocalRing.closedPoint K : Spec (CommRingCat.of K))} =
      Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have hconn := E.bundle.connectedFibres (IsLocalRing.closedPoint K)
  change _root_.IsConnected
    (E.f.base ⁻¹' {(IsLocalRing.closedPoint K : Spec (CommRingCat.of K))}) at hconn
  rw [hfibre] at hconn
  exact hconn

/-- The exact source geometry, using the actual identity and arbitrary field base change.
No model/connected-geometric-fibre/desired integrality premise is added. -/
theorem geometricallyIntegral {K : Type} [Field K] (E : FakeEC K) :
    GeometricallyIntegral E.f := by
  letI : Smooth E.f := E.bundle.smooth
  letI : ConnectedSpace E.A := connectedSpace E
  let Ω := AlgebraicClosure K
  let i : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  haveI : ConnectedSpace ↥(pullback E.f i) :=
    FLT.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.connectedSpace_pullback
      E.f (identitySection E) (identitySection_over E)
  haveI : Smooth (pullback.snd E.f i) := inferInstance
  haveI : IsIntegral (pullback E.f i) :=
    FLT.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.isIntegral_of_smooth_of_connectedSpace
      (pullback.snd E.f i)
  haveI : GeometricallyIntegral (pullback.snd E.f i) :=
    FLT.AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed (pullback.snd E.f i)
  haveI : GeometricallyConnected (pullback.snd E.f i) :=
    FLT.AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected (pullback.snd E.f i)
  haveI : MorphismProperty.DescendsAlong
      (@GeometricallyConnected : MorphismProperty Scheme) @Surjective :=
    FLT.AlgebraicGeometry.GeometricallyConnected.descendsAlong_surjective
  have hi : Surjective i := ⟨Function.surjective_to_subsingleton _⟩
  haveI : GeometricallyConnected E.f :=
    MorphismProperty.of_pullback_snd_of_descendsAlong
      (P := @GeometricallyConnected) (Q := @Surjective) hi inferInstance
  refine ⟨fun L _ y Z fst snd h => ?_⟩
  haveI : Smooth (pullback.snd E.f y) := inferInstance
  haveI : ConnectedSpace ↥(pullback E.f y) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd E.f y)
  haveI : IsIntegral (pullback E.f y) :=
    FLT.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.isIntegral_of_smooth_of_connectedSpace
      (pullback.snd E.f y)
  exact IsIntegral.of_isIso h.isoPullback.inv

/-- All three required properties for the SAME source morphism. -/
theorem abVarProps {K : Type} [Field K] (E : FakeEC K) : AbVarProps E :=
  ⟨E.bundle.proper, E.bundle.smooth, geometricallyIntegral E⟩

#print axioms connectedSpace
#print axioms geometricallyIntegral
#print axioms abVarProps

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D2
