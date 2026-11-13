import Mathlib

/-!
# g4-weilres, part 2: conjugating homomorphisms of base-changed group objects

Generic category theory (any `C` with pullbacks). For a monoid object `X` over `S` and two base
changes along `f₁, f₂ : T → S` with `f₂ = s ≫ f₁`, the comparison `g : X ×_{S,f₂} T → X ×_{S,f₁} T`
(over `s : T → T`) respects the multiplications, and the conjugate of a monoid homomorphism along
`g` (the unique lift through the pullback square) is a monoid homomorphism.
In the application `S = Spec K`, `T = Spec ℚ̄`, `f₁ = Spec e`, `s = Spec σ`, `f₂ = Spec (σ ∘ e)`.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Obj

namespace G4Conj

variable {C : Type*} [Category C] [HasPullbacks C] {S T : C}

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

/-- The multiplication of the base change, followed by the projection to `X`. -/
theorem mul_left_fst (f : T ⟶ S) (X : Over S) [MonObj X] :
    (μ[(Over.pullback f).obj X]).left ≫ pullback.fst X.hom f =
      pullback.lift (pullback.fst _ _ ≫ pullback.fst X.hom f)
        (pullback.snd _ _ ≫ pullback.fst X.hom f)
        (by
          simp only [Category.assoc, pullback.condition]
          exact pullback.condition_assoc f) ≫ μ[X].left := by
  show ((Functor.LaxMonoidal.μ (Over.pullback f) X X) ≫ (Over.pullback f).map μ[X]).left ≫ _ = _
  rw [Over.comp_left, Category.assoc]
  erw [pullback.lift_fst]
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    exact Over.μ_pullback_left_fst_fst X X
  · simp only [Category.assoc, pullback.lift_snd]
    exact Over.μ_pullback_left_fst_snd X X

end G4Conj
