import Mathlib

/-!
# The valuative criterion as a bijection of points

Let `f : X ⟶ Y` be a morphism of schemes that satisfies the valuative criterion, for instance a
proper morphism (Mathlib's `IsProper.eq_valuativeCriterion`, Stacks 0BX5). Let `R` be a valuation
ring with fraction field `K`, and let `y : Spec R ⟶ Y`. Restriction along `Spec K ⟶ Spec R` is then
a bijection from the `R`-points of `X` over `y` to the `K`-points of `X` over the restriction of
`y` (`restrictPt_bijective`, `restrictEquiv`).

Existence of the lift is the existence part of the criterion and injectivity is its uniqueness
part. Nothing here is specific to `p`-adic rings.
-/

open CategoryTheory AlgebraicGeometry Limits

set_option linter.unusedSectionVars false

noncomputable section

namespace ZInQ.Contrib.ColmezProperModel

universe u

section Valuative

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (R K : Type u) [CommRing R] [IsDomain R]
  [ValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- `Spec K ⟶ Spec R`. -/
abbrev specFrac : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The `R`-points of `X` over `y : Spec R ⟶ Y`. -/
abbrev IntPts (y : Spec (CommRingCat.of R) ⟶ Y) : Type u :=
  {x : Spec (CommRingCat.of R) ⟶ X // x ≫ f = y}

/-- The `K`-points of `X` over `specFrac R K ≫ y`. -/
abbrev FracPts (y : Spec (CommRingCat.of R) ⟶ Y) : Type u :=
  {z : Spec (CommRingCat.of K) ⟶ X // z ≫ f = specFrac R K ≫ y}

/-- Restriction of an `R`-point of `X` over `y` to a `K`-point. -/
def restrictPt (y : Spec (CommRingCat.of R) ⟶ Y) (x : IntPts f R y) : FracPts f R K y :=
  ⟨specFrac R K ≫ x.1, by rw [Category.assoc, x.2]⟩

theorem restrictPt_coe (y : Spec (CommRingCat.of R) ⟶ Y) (x : IntPts f R y) :
    (restrictPt f R K y x).1 = specFrac R K ≫ x.1 := rfl

/-- A proper morphism satisfies the valuative criterion (Mathlib, Stacks 0BX5). -/
theorem valuativeCriterion_of_isProper [IsProper f] : ValuativeCriterion f := by
  have h : IsProper f := inferInstance
  rw [IsProper.eq_valuativeCriterion] at h
  exact h.1.1.1

/-- The valuative square attached to a `K`-point over `specFrac R K ≫ y`. -/
def valSq (y : Spec (CommRingCat.of R) ⟶ Y) (z : FracPts f R K y) : ValuativeCommSq f where
  R := R
  K := K
  i₁ := z.1
  i₂ := y
  commSq := ⟨z.2⟩

/-- **The valuative criterion as a bijection**: `X(R)_y → X(K)_y` is bijective. -/
theorem restrictPt_bijective (hf : ValuativeCriterion f) (y : Spec (CommRingCat.of R) ⟶ Y) :
    Function.Bijective (restrictPt f R K y) := by
  constructor
  · intro x₁ x₂ h
    have h1 : specFrac R K ≫ x₁.1 = specFrac R K ≫ x₂.1 := congrArg Subtype.val h
    obtain ⟨hu⟩ := hf (valSq f R K y (restrictPt f R K y x₁))
    let l₁ : (valSq f R K y (restrictPt f R K y x₁)).commSq.LiftStruct := ⟨x₁.1, rfl, x₁.2⟩
    let l₂ : (valSq f R K y (restrictPt f R K y x₁)).commSq.LiftStruct := ⟨x₂.1, h1.symm, x₂.2⟩
    exact Subtype.ext (congrArg CommSq.LiftStruct.l ((hu.uniq l₁).trans (hu.uniq l₂).symm))
  · intro z
    obtain ⟨hu⟩ := hf (valSq f R K y z)
    exact ⟨⟨hu.default.l, hu.default.fac_right⟩, Subtype.ext hu.default.fac_left⟩

/-- `X(R)_y ≃ X(K)_y` for `f` satisfying the valuative criterion. -/
def restrictEquiv (hf : ValuativeCriterion f) (y : Spec (CommRingCat.of R) ⟶ Y) :
    IntPts f R y ≃ FracPts f R K y :=
  Equiv.ofBijective _ (restrictPt_bijective f R K hf y)

theorem restrictEquiv_apply (hf : ValuativeCriterion f) (y : Spec (CommRingCat.of R) ⟶ Y)
    (x : IntPts f R y) : restrictEquiv f R K hf y x = restrictPt f R K y x := rfl

end Valuative

end ZInQ.Contrib.ColmezProperModel

end
