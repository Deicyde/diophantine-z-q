import Mathlib
import ZInQKernel.HDecomp.B3Unram.B3b
import ZInQKernel.HDecomp.Objects

section ConjSec

/-!
## Part A: conjugating homomorphisms of base-changed group objects

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

/-- The comparison square over `s` is a pullback. -/
theorem cmp_isPullback :
    IsPullback (cmp X s h) (pullback.snd X.hom f₂) (pullback.snd X.hom f₁) s := by
  have sq : IsPullback (pullback.fst X.hom f₂) (pullback.snd X.hom f₂) X.hom (s ≫ f₁) := by
    rw [← h]; exact IsPullback.of_hasPullback _ _
  have e : cmp X s h = (IsPullback.of_hasPullback X.hom f₁).lift (pullback.fst X.hom f₂)
      (pullback.snd X.hom f₂ ≫ s) (by rw [sq.w, Category.assoc]) := by
    apply pullback.hom_ext
    · rw [cmp_fst]; exact (IsPullback.lift_fst _ _ _ _).symm
    · rw [cmp_snd]; exact (IsPullback.lift_snd _ _ _ _).symm
  rw [e]
  exact IsPullback.of_right' sq (IsPullback.of_hasPullback X.hom f₁)

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

variable (X Y : Over S) {f₁ f₂ g₁ g₂ : T ⟶ S} (s : T ⟶ T) (hf : f₂ = s ≫ f₁) (hg : g₂ = s ≫ g₁)

/-- Two maps into `Y ×_{g₂} T` agreeing after `cmp` and after the structure map are equal. -/
theorem ext_cmp {Z : C} (a b : Z ⟶ pullback Y.hom g₂) (h1 : a ≫ cmp Y s hg = b ≫ cmp Y s hg)
    (h2 : a ≫ pullback.snd Y.hom g₂ = b ≫ pullback.snd Y.hom g₂) : a = b := by
  apply pullback.hom_ext _ h2
  rw [← cmp_fst Y s hg, ← Category.assoc, h1, Category.assoc]

/-- **The conjugate of a morphism** `φ : X_{f₁} → Y_{g₁}` (over `T`): the morphism
`X_{f₂} → Y_{g₂}` with `σφ ∘ cmp = cmp ∘ φ` (`conj_cmp`), unique (`conj_unique`). -/
noncomputable def conj (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) :
    (Over.pullback f₂).obj X ⟶ (Over.pullback g₂).obj Y :=
  Over.homMk (pullback.lift (cmp X s hf ≫ φ.left ≫ pullback.fst Y.hom g₁)
    (pullback.snd X.hom f₂) (by
      rw [Category.assoc, Category.assoc, pullback.condition]
      have hw : φ.left ≫ pullback.snd Y.hom g₁ = pullback.snd X.hom f₁ := Over.w φ
      rw [reassoc_of% hw, cmp_snd_assoc, hg]))
    (pullback.lift_snd _ _ _)

@[reassoc]
theorem conj_cmp (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) :
    (conj X Y s hf hg φ).left ≫ cmp Y s hg = cmp X s hf ≫ φ.left := by
  apply pullback.hom_ext
  · simp only [Category.assoc, cmp_fst]
    exact pullback.lift_fst _ _ _
  · simp only [Category.assoc, cmp_snd]
    have hw : φ.left ≫ pullback.snd Y.hom g₁ = pullback.snd X.hom f₁ := Over.w φ
    rw [hw, cmp_snd]
    exact pullback.lift_snd_assoc _ _ _ _

theorem conj_unique (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y)
    (ψ : (Over.pullback f₂).obj X ⟶ (Over.pullback g₂).obj Y)
    (hψ : ψ.left ≫ cmp Y s hg = cmp X s hf ≫ φ.left) : ψ = conj X Y s hf hg φ := by
  apply Over.OverMorphism.ext
  apply ext_cmp Y s hg
  · rw [hψ, conj_cmp]
  · exact (Over.w ψ).trans (Over.w (conj X Y s hf hg φ)).symm

theorem tensor_cmp2 (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) :
    (conj X Y s hf hg φ ⊗ₘ conj X Y s hf hg φ).left ≫ cmp2 Y s hg =
      cmp2 X s hf ≫ (φ ⊗ₘ φ).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, cmp2_fst, Category.assoc]
    erw [Over.tensorHom_left_fst_assoc, Over.tensorHom_left_fst]
    rw [conj_cmp, cmp2_fst_assoc]
  · rw [Category.assoc, cmp2_snd, Category.assoc]
    erw [Over.tensorHom_left_snd_assoc, Over.tensorHom_left_snd]
    rw [conj_cmp, cmp2_snd_assoc]

/-- **The conjugate of a monoid homomorphism is a monoid homomorphism.** -/
theorem conj_isMonHom [MonObj X] [MonObj Y]
    (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) [IsMonHom φ] :
    IsMonHom (conj X Y s hf hg φ) where
  one_hom := by
    apply Over.OverMorphism.ext
    apply ext_cmp Y s hg
    · rw [Over.comp_left, Category.assoc, conj_cmp, ← Category.assoc, cmp_one, Category.assoc,
        ← Over.comp_left, IsMonHom.one_hom, cmp_one]
    · exact (Over.w _).trans (Over.w _).symm
  mul_hom := by
    apply Over.OverMorphism.ext
    apply ext_cmp Y s hg
    · rw [Over.comp_left, Category.assoc, conj_cmp, ← Category.assoc, cmp_mul, Category.assoc,
        ← Over.comp_left, IsMonHom.mul_hom, Over.comp_left, Over.comp_left, Category.assoc,
        cmp_mul, reassoc_of% (tensor_cmp2 X Y s hf hg φ)]
    · exact (Over.w _).trans (Over.w _).symm

/-- `conj_isMonHom` with the hypothesis explicit (for instances found only up to unfolding). -/
theorem conj_isMonHom' [MonObj X] [MonObj Y]
    (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) (hφ : IsMonHom φ) :
    IsMonHom (conj X Y s hf hg φ) :=
  conj_isMonHom X Y s hf hg φ

theorem lift_cmp2 (φ ψ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) :
    (lift (conj X Y s hf hg φ) (conj X Y s hf hg ψ)).left ≫ cmp2 Y s hg =
      cmp X s hf ≫ (lift φ ψ).left := by
  rw [Over.lift_left, Over.lift_left]
  apply pullback.hom_ext
  · rw [Category.assoc, cmp2_fst, pullback.lift_fst_assoc, Category.assoc, pullback.lift_fst,
      conj_cmp]
  · rw [Category.assoc, cmp2_snd, pullback.lift_snd_assoc, Category.assoc, pullback.lift_snd,
      conj_cmp]

/-- **Conjugation is multiplicative** for the pointwise product of morphisms into a monoid. -/
theorem conj_mul [MonObj Y] (φ ψ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) :
    conj X Y s hf hg (φ * ψ) = conj X Y s hf hg φ * conj X Y s hf hg ψ := by
  symm
  apply conj_unique
  rw [Hom.mul_def, Hom.mul_def, Over.comp_left, Over.comp_left, Category.assoc, cmp_mul,
    ← Category.assoc, lift_cmp2, Category.assoc]

theorem conj_one [MonObj Y] :
    conj X Y s hf hg (1 : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) = 1 := by
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
  exact (cmp_snd X s hf).symm

/-- Conjugation along equal maps `s = s'` agrees. -/
theorem conj_congr {s' : T ⟶ T} (hs : s = s') (hf' : f₂ = s' ≫ f₁) (hg' : g₂ = s' ≫ g₁)
    (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) :
    conj X Y s hf hg φ = conj X Y s' hf' hg' φ := by
  subst hs; rfl

/-- `cmp` along the identity is the identity. -/
theorem cmp_self (hs : s = 𝟙 T) (hf₀ : f₁ = s ≫ f₁) : cmp X s hf₀ = 𝟙 _ := by
  apply pullback.hom_ext
  · simp
  · rw [cmp_snd, hs, Category.comp_id, Category.id_comp]

/-- Conjugation along the identity is the identity. -/
theorem conj_self (hs : s = 𝟙 T) (hf₀ : f₁ = s ≫ f₁) (hg₀ : g₁ = s ≫ g₁)
    (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) :
    conj X Y s hf₀ hg₀ φ = φ := by
  symm
  apply conj_unique
  rw [cmp_self X s hs hf₀, cmp_self Y s hs hg₀]
  erw [Category.comp_id, Category.id_comp]

/-- `cmp` composes. -/
theorem cmp_comp {f₃ : T ⟶ S} (s' : T ⟶ T) (h₃₂ : f₃ = s' ≫ f₂) (h₃₁ : f₃ = (s' ≫ s) ≫ f₁) :
    cmp X (s' ≫ s) h₃₁ = cmp X s' h₃₂ ≫ cmp X s hf := by
  apply pullback.hom_ext
  · simp
  · simp

/-- **Conjugation composes.** -/
theorem conj_comp {f₃ g₃ : T ⟶ S} (s' : T ⟶ T) (hf₃₂ : f₃ = s' ≫ f₂) (hg₃₂ : g₃ = s' ≫ g₂)
    (hf₃₁ : f₃ = (s' ≫ s) ≫ f₁) (hg₃₁ : g₃ = (s' ≫ s) ≫ g₁)
    (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) :
    conj X Y (s' ≫ s) hf₃₁ hg₃₁ φ = conj X Y s' hf₃₂ hg₃₂ (conj X Y s hf hg φ) := by
  symm
  apply conj_unique
  rw [cmp_comp Y s hg s' hg₃₂ hg₃₁, cmp_comp X s hf s' hf₃₂ hf₃₁, conj_cmp_assoc, conj_cmp,
    Category.assoc]

end ConjMor

end G4Conj

end ConjSec

section NewConj

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Obj

namespace G4Conj

variable {C : Type*} [Category C] [HasPullbacks C] {S T : C}

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

section Agree

variable (X Y : Over S) {f g : T ⟶ S} (s : T ⟶ T) (hf : f = s ≫ f) (hg : g = s ≫ g)

/-- **Equivariance on test points.** If a test point `Q : Z → X_f` and its image `Q ≫ φ` are
fixed by conjugation (relative to a lift `s'` of `s` on `Z`), then `σφ` and `φ` agree on `Q`. -/
theorem conj_agree (φ : (Over.pullback f).obj X ⟶ (Over.pullback g).obj Y) {Z : C}
    (Q : Z ⟶ pullback X.hom f) (s' : Z ⟶ Z)
    (hQ : Q ≫ cmp X s hf = s' ≫ Q)
    (hφQ : Q ≫ φ.left ≫ cmp Y s hg = s' ≫ Q ≫ φ.left) :
    Q ≫ (conj X Y s hf hg φ).left = Q ≫ φ.left := by
  apply pullback.hom_ext
  · have e1 : Q ≫ (conj X Y s hf hg φ).left ≫ pullback.fst Y.hom g =
        Q ≫ (conj X Y s hf hg φ).left ≫ cmp Y s hg ≫ pullback.fst Y.hom g := by
      rw [cmp_fst]
    have e2 : Q ≫ φ.left ≫ pullback.fst Y.hom g =
        Q ≫ φ.left ≫ cmp Y s hg ≫ pullback.fst Y.hom g := by
      rw [cmp_fst]
    rw [Category.assoc, Category.assoc, e1, e2, conj_cmp_assoc, reassoc_of% hQ,
      reassoc_of% hφQ]
  · rw [Category.assoc, Category.assoc]
    have h1 : (conj X Y s hf hg φ).left ≫ pullback.snd Y.hom g = pullback.snd X.hom f :=
      Over.w _
    have h2 : φ.left ≫ pullback.snd Y.hom g = pullback.snd X.hom f := Over.w φ
    rw [h1, h2]

/-- A section `Q` of `X_f` is fixed by conjugation iff its `X`-component is fixed by `s`. -/
theorem cmp_fixed_of_fst (Q : T ⟶ pullback X.hom f) (hQ : Q ≫ pullback.snd X.hom f = 𝟙 T)
    (h : s ≫ Q ≫ pullback.fst X.hom f = Q ≫ pullback.fst X.hom f) :
    Q ≫ cmp X s hf = s ≫ Q := by
  apply pullback.hom_ext
  · rw [Category.assoc, cmp_fst, Category.assoc, h]
  · rw [Category.assoc, cmp_snd, reassoc_of% hQ, Category.assoc, hQ]
    simp

end Agree

section Sections

variable (X : Over S) [MonObj X] (f : T ⟶ S)

/-- The `X`-component of a section of `X_f`, as a point of `X` over `S` with source `T` (via `f`). -/
noncomputable def secFst (Q : Over.mk (𝟙 T) ⟶ (Over.pullback f).obj X) : Over.mk f ⟶ X :=
  Over.homMk (Q.left ≫ pullback.fst X.hom f) (by
    rw [Category.assoc, pullback.condition]
    have hw : Q.left ≫ pullback.snd X.hom f = 𝟙 T := Over.w Q
    rw [reassoc_of% hw]
    simp)

omit [MonObj X] in
@[simp] theorem secFst_left (Q : Over.mk (𝟙 T) ⟶ (Over.pullback f).obj X) :
    (secFst X f Q).left = Q.left ≫ pullback.fst X.hom f := rfl

theorem secFst_mul (Q R : Over.mk (𝟙 T) ⟶ (Over.pullback f).obj X) :
    secFst X f (Q * R) = secFst X f Q * secFst X f R := by
  apply Over.OverMorphism.ext
  rw [secFst_left, Hom.mul_def, Hom.mul_def, Over.comp_left, Over.comp_left, Category.assoc,
    mul_left_fst, ← Category.assoc]
  congr 1
  rw [Over.lift_left, Over.lift_left]
  apply pullback.hom_ext
  · simp
  · simp

theorem secFst_one : secFst X f (1 : Over.mk (𝟙 T) ⟶ (Over.pullback f).obj X) = 1 := by
  apply Over.OverMorphism.ext
  rw [secFst_left, Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Category.assoc,
    one_left_fst, Over.toUnit_left, Over.toUnit_left]
  simp

/-- `secFst` as a monoid homomorphism. -/
noncomputable def secFstHom : (Over.mk (𝟙 T) ⟶ (Over.pullback f).obj X) →* (Over.mk f ⟶ X) where
  toFun := secFst X f
  map_one' := secFst_one X f
  map_mul' := secFst_mul X f

theorem secFst_pow (Q : Over.mk (𝟙 T) ⟶ (Over.pullback f).obj X) (n : ℕ) :
    secFst X f (Q ^ n) = secFst X f Q ^ n :=
  map_pow (secFstHom X f) Q n

end Sections

end G4Conj

end NewConj

namespace InertiaHoms

open GlueB3Unram
open scoped Pointwise

/-! ## Inertia membership in terms of the valuation subring alone -/

section InertiaChar

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- `v_w(x) < 1` in terms of membership only. -/
theorem valuation_lt_one_iff_mem (w : ValuationSubring L) (x : L) :
    w.valuation x < 1 ↔ x = 0 ∨ x⁻¹ ∉ w := by
  by_cases hx : x = 0
  · simp [hx]
  · simp only [hx, false_or]
    rw [← w.valuation_le_one_iff, not_le, Valuation.one_lt_val_iff _ (inv_ne_zero hx), inv_inv]

/-- **Inertia, elementwise.** `σ` lies in the inertia group of `w` (Mathlib's
`decompositionSubgroup`/`inertiaSubgroup`) iff `σ` preserves `w` and `σ x - x` lies in the
maximal ideal of `w` for every `x ∈ w` (the latter written by membership only). -/
theorem isInertia_iff (w : ValuationSubring L) (σ : L ≃ₐ[F] L) :
    (∃ h : σ ∈ w.decompositionSubgroup F, (⟨σ, h⟩ : w.decompositionSubgroup F) ∈
        w.inertiaSubgroup F) ↔
      (∀ x, σ x ∈ w ↔ x ∈ w) ∧ (∀ x ∈ w, σ x - x = 0 ∨ (σ x - x)⁻¹ ∉ w) := by
  have hinv : ∀ x, σ⁻¹ (σ x) = x := fun x => by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel]; rfl
  have hinv' : ∀ x, σ (σ⁻¹ x) = x := fun x => by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel]; rfl
  constructor
  · rintro ⟨h, hin⟩
    have hstab : σ • w = w := h
    have hmem : ∀ y, y ∈ w ↔ σ⁻¹ y ∈ w := fun y => by
      conv_lhs => rw [← hstab]
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    have hD : ∀ x, σ x ∈ w ↔ x ∈ w := fun x => by rw [hmem (σ x), hinv]
    refine ⟨hD, fun x hx => ?_⟩
    rw [← valuation_lt_one_iff_mem]
    have hk := congrArg (fun φ : RingAut (IsLocalRing.ResidueField w) =>
      φ (IsLocalRing.residue w ⟨x, hx⟩)) (MonoidHom.mem_ker.mp hin)
    simp only [RingAut.one_apply, MulSemiringAction.toRingAut_apply] at hk
    change (⟨σ, h⟩ : w.decompositionSubgroup F) • IsLocalRing.residue w ⟨x, hx⟩ = _ at hk
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at hk
    exact hk
  · rintro ⟨hD, hI⟩
    have hstab : σ • w = w := by
      ext y
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← hD, hinv']
    have hdec : σ ∈ w.decompositionSubgroup F := hstab
    refine ⟨hdec, ?_⟩
    unfold ValuationSubring.inertiaSubgroup
    rw [MonoidHom.mem_ker]
    apply RingEquiv.ext
    intro r
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    change (⟨σ, hdec⟩ : w.decompositionSubgroup F) • IsLocalRing.residue w a =
      IsLocalRing.residue w a
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    rw [valuation_lt_one_iff_mem]
    exact hI a.1 a.2

end InertiaChar

section Transport

/-- **Inertia transports along a ring isomorphism.** If `s` satisfies the elementwise inertia
conditions at `w`, then `ι⁻¹ ∘ s ∘ ι` satisfies them at `w.comap ι`. -/
theorem inertia_transport {L₁ L₂ : Type*} [Field L₁] [Field L₂] (ι : L₁ ≃+* L₂)
    (w : ValuationSubring L₂) (s : L₂ ≃+* L₂)
    (hD : ∀ x, s x ∈ w ↔ x ∈ w) (hI : ∀ x ∈ w, s x - x = 0 ∨ (s x - x)⁻¹ ∉ w) :
    (∀ x, ι.symm (s (ι x)) ∈ w.comap (ι : L₁ →+* L₂) ↔ x ∈ w.comap (ι : L₁ →+* L₂)) ∧
      (∀ x ∈ w.comap (ι : L₁ →+* L₂), ι.symm (s (ι x)) - x = 0 ∨
        (ι.symm (s (ι x)) - x)⁻¹ ∉ w.comap (ι : L₁ →+* L₂)) := by
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · simp only [ValuationSubring.mem_comap, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    exact hD _
  · rw [ValuationSubring.mem_comap] at hx
    have key : ι (ι.symm (s (ι x)) - x) = s (ι x) - ι x := by
      rw [map_sub, RingEquiv.apply_symm_apply]
    rcases hI _ hx with h | h
    · left
      apply ι.injective
      have h' : s (ι x) - ι x = 0 := h
      rw [key, h', map_zero]
    · right
      rw [ValuationSubring.mem_comap, RingEquiv.coe_toRingHom, map_inv₀, key]
      exact h

end Transport

section Closure

/-- `ℚ̄` is an algebraic closure of `K` through any embedding `e : K → ℚ̄`: a ring isomorphism
`ι : K̄ ≃ ℚ̄` extending `e`. -/
theorem exists_closure_equiv (K : IntermediateField ℚ Qbar) (e : K →ₐ[ℚ] Qbar) :
    ∃ ι : AlgebraicClosure K ≃+* Qbar, ∀ x, ι (algebraMap K (AlgebraicClosure K) x) = e x := by
  let R : IntermediateField ℚ Qbar := e.fieldRange
  let hSR : K ≃+* R := (AlgEquiv.ofInjectiveField e).toRingEquiv
  have : Algebra.IsAlgebraic R Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) R
  have : IsAlgClosure R Qbar := ⟨inferInstance, inferInstance⟩
  refine ⟨IsAlgClosure.equivOfEquiv (AlgebraicClosure K) Qbar hSR, fun x => ?_⟩
  rw [IsAlgClosure.equivOfEquiv_algebraMap]
  rfl

end Closure

section Unit

/-- At a place over `p`, every prime `ℓ ≠ p` is a unit of the valuation ring (of any subfield). -/
theorem isUnit_prime_of_liesOver {F : Type*} [Field F] [CharZero F] (f : F →+* Qbar)
    (w : ValuationSubring Qbar) (p : ℕ) (hp : p.Prime) (hw : LiesOver w p)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hne : ℓ ≠ p) : IsUnit ((ℓ : ℕ) : w.comap f) := by
  have hcop : IsCoprime (ℓ : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hℓ hp).mpr hne)
  obtain ⟨a, b, hab⟩ := hcop
  have hpw : ((p : w) : Qbar) = p := by simp
  have hℓw : ((ℓ : w) : Qbar) = ℓ := by simp
  have hpm : (p : w) ∈ IsLocalRing.maximalIdeal w := by
    rw [ValuationSubring.valuation_lt_one_iff, hpw]; exact hw
  have hv1 : w.valuation (ℓ : Qbar) = 1 := by
    rcases w.valuation_lt_one_or_eq_one (ℓ : w) with h | h
    · exfalso
      have hℓm : (ℓ : w) ∈ IsLocalRing.maximalIdeal w := by
        rw [ValuationSubring.valuation_lt_one_iff]; exact h
      have h1 : (1 : w) ∈ IsLocalRing.maximalIdeal w := by
        have : ((a : w) * (ℓ : w) + (b : w) * (p : w)) = 1 := by
          have := congrArg (Int.cast : ℤ → w) hab
          push_cast at this
          exact this
        rw [← this]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hℓm) (Ideal.mul_mem_left _ _ hpm)
      exact (IsLocalRing.maximalIdeal.isMaximal w).ne_top
        ((Ideal.eq_top_iff_one _).mpr h1)
    · rw [← hℓw]; exact h
  have hℓF : (ℓ : F) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
  have hinv : (ℓ : F)⁻¹ ∈ w.comap f := by
    rw [ValuationSubring.mem_comap, map_inv₀, map_natCast, ← w.valuation_le_one_iff, map_inv₀,
      hv1, inv_one]
  refine isUnit_iff_exists_inv.mpr ⟨⟨(ℓ : F)⁻¹, hinv⟩, ?_⟩
  apply Subtype.ext
  simp [hℓF]

end Unit

end InertiaHoms

-- BEGIN STUB (copies of G4 definitions; dropped when merged after G4.lean)
namespace G4WeilRes
open GlueB3Unram AlgebraicGeometry
noncomputable abbrev specGal (σ : Gal) :
    Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of Qbar) :=
  Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar))
variable (K : IntermediateField ℚ Qbar)
noncomputable abbrev specEmb (e : K →ₐ[ℚ] Qbar) :
    Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (e : K →+* Qbar))
end G4WeilRes
-- END STUB

namespace G4WeilRes

open GlueB3Unram CategoryTheory AlgebraicGeometry Limits MonObj PkgI3 InertiaHoms

variable (K : IntermediateField ℚ Qbar)

theorem specMap_comp {R S U : Type} [CommRing R] [CommRing S] [CommRing U] (a : R →+* S)
    (b : S →+* U) :
    Spec.map (CommRingCat.ofHom b) ≫ Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom (b.comp a)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- **Inertia fixes prime-to-`p` torsion points of a conjugate (NOS, transported).** Let `A/K`
have good reduction at `w ∩ e(K)` (a DVR), `s ∈ I_w` fix `e(K)`, and `m` be invertible at `w`.
A point `q : Spec ℚ̄ → A` over `Spec e` with `q^m = 1` is fixed by `s`: `Spec s ≫ q = q`.
Leaf: `PkgI2.NeronOggShafarevich` (Serre–Tate 1968 Thm 1), applied to `A/K` at `w ∩ e(K)`, with
`ℚ̄ ≅ K̄` extending `e` and the inertia group transported along it. -/
theorem point_fixed (hNOS : PkgI2.NeronOggShafarevich.{0})
    (A : AbVar K) (e : K →ₐ[ℚ] Qbar) (w : ValuationSubring Qbar)
    [IsDiscreteValuationRing (w.comap (e : K →+* Qbar))]
    (hgood : PkgI2.HasGoodReduction (ObjBridge.toGrp A) (w.comap (e : K →+* Qbar)))
    (s : Gal) (hs : s ∈ inertiaGQ w) (hse : ∀ x, s (e x) = e x)
    (m : ℕ) (hm : 0 < m) (hmO : IsUnit ((m : ℕ) : w.comap (e : K →+* Qbar)))
    (q : CategoryTheory.Over.mk (specEmb K e) ⟶ A.X) (hq : q ^ m = 1) :
    specGal s ≫ q.left = q.left := by
  obtain ⟨ie, hie⟩ := exists_closure_equiv K e
  have hies : ∀ x : K, ie.symm (e x) = algebraMap K (AlgebraicClosure K) x := fun x => by
    rw [← hie, RingEquiv.symm_apply_apply]
  let σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
    AlgEquiv.ofRingEquiv (f := (ie.trans s.toRingEquiv).trans ie.symm) (fun x => by
      simp only [RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, hie, hse, hies])
  have hσ : ∀ x, σ x = ie.symm (s (ie x)) := fun x => rfl
  let w' : ValuationSubring (AlgebraicClosure K) := w.comap (ie : AlgebraicClosure K →+* Qbar)
  have hw' : w'.comap (algebraMap K (AlgebraicClosure K)) = w.comap (e : K →+* Qbar) := by
    ext x
    simp only [w', ValuationSubring.mem_comap, RingEquiv.coe_toRingHom]
    rw [hie]
    rfl
  have hsI : (∀ x, s x ∈ w ↔ x ∈ w) ∧ (∀ x ∈ w, s x - x = 0 ∨ (s x - x)⁻¹ ∉ w) := by
    obtain ⟨g, hg, hgs⟩ := Subgroup.mem_map.mp hs
    have := (isInertia_iff w g.1).mp ⟨g.2, hg⟩
    rw [← hgs]
    exact this
  have hIσ : PkgI2.IsInertia w' σ := by
    rw [PkgI2.IsInertia, isInertia_iff]
    exact inertia_transport ie w s.toRingEquiv hsI.1 hsI.2
  let J : PkgI2.specOver K (AlgebraicClosure K) ⟶ CategoryTheory.Over.mk (specEmb K e) :=
    CategoryTheory.Over.homMk
      (Spec.map (CommRingCat.ofHom (ie.symm : Qbar →+* AlgebraicClosure K))) (by
        show Spec.map _ ≫ Spec.map _ = Spec.map _
        rw [specMap_comp]
        congr 2
        ext x
        exact hies x)
  let x : PkgI2.Pts (ObjBridge.toGrp A) (AlgebraicClosure K) := J ≫ q
  have hx : x ∈ PkgI2.torsion (ObjBridge.toGrp A) (AlgebraicClosure K) m := by
    show (J ≫ q) ^ m = 1
    rw [← MonObj.comp_pow, hq, MonObj.comp_one]
  have hfix := ((hNOS K (w.comap (e : K →+* Qbar)) w' hw' (ObjBridge.toGrp A)).1.mp hgood)
    m hm hmO σ hIσ x hx
  have h2 : Spec.map (CommRingCat.ofHom (ie : AlgebraicClosure K →+* Qbar)) ≫
      Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫
      Spec.map (CommRingCat.ofHom (ie.symm : Qbar →+* AlgebraicClosure K)) ≫ q.left =
      Spec.map (CommRingCat.ofHom (ie : AlgebraicClosure K →+* Qbar)) ≫
      Spec.map (CommRingCat.ofHom (ie.symm : Qbar →+* AlgebraicClosure K)) ≫ q.left := by
    have := congrArg (fun t => Spec.map (CommRingCat.ofHom (ie : AlgebraicClosure K →+* Qbar)) ≫
      CategoryTheory.Over.Hom.left t) hfix
    exact this
  rw [← Category.assoc, ← Category.assoc, specMap_comp, specMap_comp, ← Category.assoc,
    specMap_comp] at h2
  have e1 : ((ie : AlgebraicClosure K →+* Qbar).comp
      (σ : AlgebraicClosure K →+* AlgebraicClosure K)).comp
      (ie.symm : Qbar →+* AlgebraicClosure K) = (s : Qbar →+* Qbar) := by
    ext y
    simp [hσ]
  have e2 : (ie : AlgebraicClosure K →+* Qbar).comp (ie.symm : Qbar →+* AlgebraicClosure K) =
      RingHom.id Qbar := by
    ext y
    simp
  rw [e1, e2] at h2
  rw [h2, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

end G4WeilRes
