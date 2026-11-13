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


/-! ### Conjugating morphisms -/

section ConjMor

variable (X Y : Over S) {f₁ f₂ : T ⟶ S} (s : T ⟶ T) (h : f₂ = s ≫ f₁)

/-- Two maps into `Y ×_{f₂} T` agreeing after `cmp` and after the structure map are equal. -/
theorem ext_cmp {Z : C} (a b : Z ⟶ pullback Y.hom f₂) (h1 : a ≫ cmp Y s h = b ≫ cmp Y s h)
    (h2 : a ≫ pullback.snd Y.hom f₂ = b ≫ pullback.snd Y.hom f₂) : a = b := by
  apply pullback.hom_ext _ h2
  rw [← cmp_fst Y s h, ← Category.assoc, h1, Category.assoc]

/-- **The conjugate of a morphism** `φ : X_{f₁} → Y_{f₁}` (over `T`): the morphism
`X_{f₂} → Y_{f₂}` with `σφ ∘ cmp = cmp ∘ φ` (`conj_cmp`), unique (`conj_unique`). -/
noncomputable def conj (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback f₁).obj Y) :
    (Over.pullback f₂).obj X ⟶ (Over.pullback f₂).obj Y :=
  Over.homMk (pullback.lift (cmp X s h ≫ φ.left ≫ pullback.fst Y.hom f₁)
    (pullback.snd X.hom f₂) (by
      rw [Category.assoc, Category.assoc, pullback.condition]
      have hw : φ.left ≫ pullback.snd Y.hom f₁ = pullback.snd X.hom f₁ := Over.w φ
      rw [reassoc_of% hw, cmp_snd_assoc, h]))
    (pullback.lift_snd _ _ _)

@[reassoc]
theorem conj_cmp (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback f₁).obj Y) :
    (conj X Y s h φ).left ≫ cmp Y s h = cmp X s h ≫ φ.left := by
  apply pullback.hom_ext
  · simp only [Category.assoc, cmp_fst]
    exact pullback.lift_fst _ _ _
  · simp only [Category.assoc, cmp_snd]
    have hw : φ.left ≫ pullback.snd Y.hom f₁ = pullback.snd X.hom f₁ := Over.w φ
    rw [hw, cmp_snd]
    exact pullback.lift_snd_assoc _ _ _ _

theorem conj_unique (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback f₁).obj Y)
    (ψ : (Over.pullback f₂).obj X ⟶ (Over.pullback f₂).obj Y)
    (hψ : ψ.left ≫ cmp Y s h = cmp X s h ≫ φ.left) : ψ = conj X Y s h φ := by
  apply Over.OverMorphism.ext
  apply ext_cmp Y s h
  · rw [hψ, conj_cmp]
  · exact (Over.w ψ).trans (Over.w (conj X Y s h φ)).symm

theorem tensor_cmp2 (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback f₁).obj Y) :
    (conj X Y s h φ ⊗ₘ conj X Y s h φ).left ≫ cmp2 Y s h = cmp2 X s h ≫ (φ ⊗ₘ φ).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, cmp2_fst, Category.assoc]
    erw [Over.tensorHom_left_fst_assoc, Over.tensorHom_left_fst]
    rw [conj_cmp, cmp2_fst_assoc]
  · rw [Category.assoc, cmp2_snd, Category.assoc]
    erw [Over.tensorHom_left_snd_assoc, Over.tensorHom_left_snd]
    rw [conj_cmp, cmp2_snd_assoc]

/-- **The conjugate of a monoid homomorphism is a monoid homomorphism.** -/
theorem conj_isMonHom [MonObj X] [MonObj Y]
    (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback f₁).obj Y) [IsMonHom φ] :
    IsMonHom (conj X Y s h φ) where
  one_hom := by
    apply Over.OverMorphism.ext
    apply ext_cmp Y s h
    · rw [Over.comp_left, Category.assoc, conj_cmp, ← Category.assoc, cmp_one, Category.assoc,
        ← Over.comp_left, IsMonHom.one_hom, cmp_one]
    · exact (Over.w _).trans (Over.w _).symm
  mul_hom := by
    apply Over.OverMorphism.ext
    apply ext_cmp Y s h
    · rw [Over.comp_left, Category.assoc, conj_cmp, ← Category.assoc, cmp_mul, Category.assoc,
        ← Over.comp_left, IsMonHom.mul_hom, Over.comp_left, Over.comp_left, Category.assoc,
        cmp_mul, reassoc_of% (tensor_cmp2 X Y s h φ)]
    · exact (Over.w _).trans (Over.w _).symm

theorem lift_cmp2 (φ ψ : (Over.pullback f₁).obj X ⟶ (Over.pullback f₁).obj Y) :
    (lift (conj X Y s h φ) (conj X Y s h ψ)).left ≫ cmp2 Y s h =
      cmp X s h ≫ (lift φ ψ).left := by
  rw [Over.lift_left, Over.lift_left]
  apply pullback.hom_ext
  · rw [Category.assoc, cmp2_fst, pullback.lift_fst_assoc, Category.assoc, pullback.lift_fst,
      conj_cmp]
  · rw [Category.assoc, cmp2_snd, pullback.lift_snd_assoc, Category.assoc, pullback.lift_snd,
      conj_cmp]

/-- **Conjugation is multiplicative** for the pointwise product of morphisms into a monoid. -/
theorem conj_mul [MonObj Y] (φ ψ : (Over.pullback f₁).obj X ⟶ (Over.pullback f₁).obj Y) :
    conj X Y s h (φ * ψ) = conj X Y s h φ * conj X Y s h ψ := by
  symm
  apply conj_unique
  rw [Hom.mul_def, Hom.mul_def, Over.comp_left, Over.comp_left, Category.assoc, cmp_mul,
    ← Category.assoc, lift_cmp2, Category.assoc]

theorem conj_one [MonObj Y] :
    conj X Y s h (1 : (Over.pullback f₁).obj X ⟶ (Over.pullback f₁).obj Y) = 1 := by
  symm
  apply conj_unique
  rw [Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Category.assoc, cmp_one,
    ← Category.assoc, ← Category.assoc]
  congr 1
  have e1 : (toUnit ((Over.pullback f₂).obj X)).left = pullback.snd X.hom f₂ :=
    (Category.comp_id _).symm.trans (Over.w (toUnit ((Over.pullback f₂).obj X)))
  have e2 : (toUnit ((Over.pullback f₁).obj X)).left = pullback.snd X.hom f₁ :=
    (Category.comp_id _).symm.trans (Over.w (toUnit ((Over.pullback f₁).obj X)))
  rw [e1, e2]
  exact (cmp_snd X s h).symm

end ConjMor

end G4Conj
