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


/-- The unit of the base change, followed by the projection to `X`. -/
theorem one_left_fst (f : T ⟶ S) (X : Over S) [MonObj X] :
    (η[(Over.pullback f).obj X]).left ≫ pullback.fst X.hom f = f ≫ η[X].left := by
  show ((Functor.LaxMonoidal.ε (Over.pullback f)) ≫ (Over.pullback f).map η[X]).left ≫ _ = _
  rw [Over.comp_left, Category.assoc]
  erw [pullback.lift_fst]
  rw [← Category.assoc, Over.ε_pullback_left]
  congr 1
  rw [IsIso.inv_comp_eq]
  have := pullback.condition (f := 𝟙 S) (g := f)
  simpa using this

/-! ### The comparison map over `s` -/

section Cmp

variable (X : Over S) {f₁ f₂ : T ⟶ S} (s : T ⟶ T) (h : f₂ = s ≫ f₁)

/-- `X ×_{f₂} T → X ×_{f₁} T` over `s`, for `f₂ = s ≫ f₁`. -/
noncomputable def cmp : pullback X.hom f₂ ⟶ pullback X.hom f₁ :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ s)
    (by rw [pullback.condition, h, Category.assoc])

@[reassoc (attr := simp)]
theorem cmp_fst : cmp X s h ≫ pullback.fst X.hom f₁ = pullback.fst X.hom f₂ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem cmp_snd : cmp X s h ≫ pullback.snd X.hom f₁ = pullback.snd X.hom f₂ ≫ s :=
  pullback.lift_snd _ _ _

/-- `cmp` on the self-products. -/
noncomputable def cmp2 :
    ((Over.pullback f₂).obj X ⊗ (Over.pullback f₂).obj X).left ⟶
      ((Over.pullback f₁).obj X ⊗ (Over.pullback f₁).obj X).left :=
  pullback.lift (pullback.fst _ _ ≫ cmp X s h) (pullback.snd _ _ ≫ cmp X s h) (by
    show (pullback.fst _ _ ≫ cmp X s h) ≫ pullback.snd X.hom f₁ =
      (pullback.snd _ _ ≫ cmp X s h) ≫ pullback.snd X.hom f₁
    simp only [Category.assoc, cmp_snd]
    exact pullback.condition_assoc s)

@[reassoc (attr := simp)]
theorem cmp2_fst : cmp2 X s h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ cmp X s h :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem cmp2_snd : cmp2 X s h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ cmp X s h :=
  pullback.lift_snd _ _ _

/-- **The comparison respects the multiplications.** -/
theorem cmp_mul [MonObj X] :
    (μ[(Over.pullback f₂).obj X]).left ≫ cmp X s h =
      cmp2 X s h ≫ (μ[(Over.pullback f₁).obj X]).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, cmp_fst, Category.assoc, mul_left_fst, mul_left_fst,
      ← Category.assoc (cmp2 X s h)]
    congr 1
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, cmp2_fst_assoc, cmp_fst]
    · simp only [Category.assoc, pullback.lift_snd, cmp2_snd_assoc, cmp_fst]
  · rw [Category.assoc, cmp_snd, Category.assoc]
    have h2 := Over.w (μ[(Over.pullback f₂).obj X])
    have h1 := Over.w (μ[(Over.pullback f₁).obj X])
    erw [← Category.assoc, h2, h1]
    show (pullback.fst _ _ ≫ pullback.snd X.hom f₂) ≫ s =
      cmp2 X s h ≫ (pullback.fst _ _ ≫ pullback.snd X.hom f₁)
    rw [cmp2_fst_assoc, cmp_snd, Category.assoc]

/-- **The comparison respects the units.** -/
theorem cmp_one [MonObj X] :
    (η[(Over.pullback f₂).obj X]).left ≫ cmp X s h = s ≫ (η[(Over.pullback f₁).obj X]).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, cmp_fst, one_left_fst, Category.assoc, one_left_fst, h, Category.assoc]
  · rw [Category.assoc, cmp_snd, Category.assoc]
    have h2 := Over.w (η[(Over.pullback f₂).obj X])
    have h1 := Over.w (η[(Over.pullback f₁).obj X])
    erw [← Category.assoc, h2, h1]
    simp

end Cmp

end G4Conj
