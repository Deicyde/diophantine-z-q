import ZInQKernel.Contrib.OneProof.FaltingsLemma5Lower.Transport

/-! faltings5-lower, part 6: `IsogPtsSurjective`. Points with values in an algebraically closed
field lift along a finite surjective morphism (the fibre is a nonempty finite scheme over the
field, and its closed points are rational: Mathlib's `pointOfClosedPoint`). -/

set_option linter.style.haveILetI false

namespace GapHeight

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings

section Lift

variable {K : Type} [Field K]

/-- **Lifting points along a finite surjective morphism.** -/
theorem lift_pts {X Y : Over (Spec (CommRingCat.of K))} (φ : X ⟶ Y) [IsFinite φ.left]
    [Surjective φ.left] {Ω : Type} [Field Ω] [IsAlgClosed Ω] (σ : K →+* Ω) :
    Function.Surjective fun P : ptK σ ⟶ X => P ≫ φ := by
  intro q
  let Z : Scheme := pullback φ.left q.left
  let π : Z ⟶ Spec (CommRingCat.of Ω) := pullback.snd φ.left q.left
  haveI : IsFinite π :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsFinite)
      (IsPullback.of_hasPullback φ.left q.left) inferInstance
  haveI : Surjective π :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective)
      (IsPullback.of_hasPullback φ.left q.left) inferInstance
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace π
  obtain ⟨z0, -⟩ := π.surjective (IsLocalRing.closedPoint Ω)
  obtain ⟨z, -, hz⟩ := (isClosed_univ (X := Z)).exists_closed_singleton ⟨z0, Set.mem_univ _⟩
  let s := pointOfClosedPoint π z hz
  have hs : s ≫ π = 𝟙 _ := pointOfClosedPoint_comp π z hz
  have hw : (s ≫ pullback.fst φ.left q.left) ≫ φ.left = q.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have h1 : s ≫ pullback.snd φ.left q.left = 𝟙 _ := hs
    rw [h1]
    exact Category.id_comp _
  refine ⟨Over.homMk (s ≫ pullback.fst φ.left q.left) ?_, ?_⟩
  · show (s ≫ pullback.fst φ.left q.left) ≫ X.hom = (ptK σ).hom
    rw [← Over.w φ, ← Category.assoc]
    erw [hw]
    exact Over.w q
  · exact Over.OverMorphism.ext hw

end Lift

/-- **`IsogPtsSurjective`, proved.** -/
theorem isogPtsSurjective : IsogPtsSurjective := by
  intro K _ _ A B φ hφ 𝒩A 𝒩B f _ he τ
  haveI := hφ.2.1
  haveI := hφ.2.2
  exact surjective_of_surjective 𝒩A 𝒩B φ f he τ (lift_pts φ τ)

end GapHeight
