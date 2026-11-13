/-! # twist-descent, part XC: comparison maps between base changes along different bases

Generic category theory (any `C` with pullbacks), generalizing `G4Conj.cmp` (one base `T`) to two
bases: for `f₂ = s ≫ f₁` with `s : T₂ ⟶ T₁`, the comparison `X ×_{S,f₂} T₂ → X ×_{S,f₁} T₁`
(`xc`), its pullback square, composition, and compatibility with base-changed endomorphisms,
units and multiplications. -/

section TwistDescentXC

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Obj

namespace TwistDescentXC

variable {C : Type*} [Category C] [HasPullbacks C] {S : C} (X : Over S)

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

/-- `X ×_{f₂} T₂ → X ×_{f₁} T₁` over `s`, for `f₂ = s ≫ f₁`. -/
noncomputable def xc {T₁ T₂ : C} {f₁ : T₁ ⟶ S} {f₂ : T₂ ⟶ S} (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    pullback X.hom f₂ ⟶ pullback X.hom f₁ :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ s)
    (by rw [pullback.condition, h, Category.assoc])

variable {T₁ T₂ T₃ : C} {f₁ : T₁ ⟶ S} {f₂ : T₂ ⟶ S} {f₃ : T₃ ⟶ S}

@[reassoc (attr := simp)]
theorem xc_fst (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    xc X s h ≫ pullback.fst X.hom f₁ = pullback.fst X.hom f₂ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem xc_snd (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    xc X s h ≫ pullback.snd X.hom f₁ = pullback.snd X.hom f₂ ≫ s := pullback.lift_snd _ _ _

/-- The comparison square over `s` is a pullback. -/
theorem xc_isPullback (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    IsPullback (xc X s h) (pullback.snd X.hom f₂) (pullback.snd X.hom f₁) s := by
  have sq : IsPullback (pullback.fst X.hom f₂) (pullback.snd X.hom f₂) X.hom (s ≫ f₁) := by
    rw [← h]; exact IsPullback.of_hasPullback _ _
  have e : xc X s h = (IsPullback.of_hasPullback X.hom f₁).lift (pullback.fst X.hom f₂)
      (pullback.snd X.hom f₂ ≫ s) (by rw [sq.w, Category.assoc]) := by
    apply pullback.hom_ext
    · rw [xc_fst]; exact (IsPullback.lift_fst _ _ _ _).symm
    · rw [xc_snd]; exact (IsPullback.lift_snd _ _ _ _).symm
  rw [e]
  exact IsPullback.of_right' sq (IsPullback.of_hasPullback X.hom f₁)

theorem xc_comp (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) (s' : T₃ ⟶ T₂) (h' : f₃ = s' ≫ f₂)
    (h'' : f₃ = (s' ≫ s) ≫ f₁) : xc X s' h' ≫ xc X s h = xc X (s' ≫ s) h'' := by
  apply pullback.hom_ext <;> simp

theorem xc_comp_eq (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) (s' : T₃ ⟶ T₂) (h' : f₃ = s' ≫ f₂)
    (t : T₃ ⟶ T₁) (ht : f₃ = t ≫ f₁) (hst : s' ≫ s = t) :
    xc X s' h' ≫ xc X s h = xc X t ht := by
  subst hst; exact xc_comp X s h s' h' ht

theorem xc_congr {s s' : T₂ ⟶ T₁} (hs : s = s') (h : f₂ = s ≫ f₁) (h' : f₂ = s' ≫ f₁) :
    xc X s h = xc X s' h' := by
  subst hs; rfl

theorem xc_self (s : T₁ ⟶ T₁) (hs : s = 𝟙 T₁) (h : f₁ = s ≫ f₁) : xc X s h = 𝟙 _ := by
  apply pullback.hom_ext
  · simp
  · rw [xc_snd, hs, Category.comp_id, Category.id_comp]

/-- `xc` intertwines base-changed endomorphisms. -/
theorem xc_map (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) (f : X ⟶ X) :
    ((Over.pullback f₂).map f).left ≫ xc X s h = xc X s h ≫ ((Over.pullback f₁).map f).left := by
  apply pullback.hom_ext
  · simp only [Category.assoc, xc_fst, Over.pullback_map_left, pullback.lift_fst, xc_fst_assoc]
  · simp only [Category.assoc, xc_snd, Over.pullback_map_left, pullback.lift_snd,
      pullback.lift_snd_assoc]

/-- `xc` on the self-products. -/
noncomputable def xc2 (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    ((Over.pullback f₂).obj X ⊗ (Over.pullback f₂).obj X).left ⟶
      ((Over.pullback f₁).obj X ⊗ (Over.pullback f₁).obj X).left :=
  pullback.lift (pullback.fst _ _ ≫ xc X s h) (pullback.snd _ _ ≫ xc X s h) (by
    show (pullback.fst _ _ ≫ xc X s h) ≫ pullback.snd X.hom f₁ =
      (pullback.snd _ _ ≫ xc X s h) ≫ pullback.snd X.hom f₁
    simp only [Category.assoc, xc_snd]
    exact pullback.condition_assoc s)

@[reassoc (attr := simp)]
theorem xc2_fst (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    xc2 X s h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ xc X s h :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem xc2_snd (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    xc2 X s h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ xc X s h :=
  pullback.lift_snd _ _ _

/-- **`xc` respects the multiplications.** -/
theorem xc_mul [MonObj X] (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    (μ[(Over.pullback f₂).obj X]).left ≫ xc X s h =
      xc2 X s h ≫ (μ[(Over.pullback f₁).obj X]).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, xc_fst, Category.assoc, G4Conj.mul_left_fst, G4Conj.mul_left_fst,
      ← Category.assoc (xc2 X s h)]
    congr 1
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, xc2_fst_assoc, xc_fst]
    · simp only [Category.assoc, pullback.lift_snd, xc2_snd_assoc, xc_fst]
  · rw [Category.assoc, xc_snd, Category.assoc]
    have h2 := Over.w (μ[(Over.pullback f₂).obj X])
    have h1 := Over.w (μ[(Over.pullback f₁).obj X])
    erw [← Category.assoc, h2, h1]
    show (pullback.fst _ _ ≫ pullback.snd X.hom f₂) ≫ s =
      xc2 X s h ≫ (pullback.fst _ _ ≫ pullback.snd X.hom f₁)
    rw [xc2_fst_assoc, xc_snd, Category.assoc]

/-- **`xc` respects the units.** -/
theorem xc_one [MonObj X] (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    (η[(Over.pullback f₂).obj X]).left ≫ xc X s h = s ≫ (η[(Over.pullback f₁).obj X]).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, xc_fst, G4Conj.one_left_fst, Category.assoc, G4Conj.one_left_fst, h,
      Category.assoc]
  · rw [Category.assoc, xc_snd, Category.assoc]
    have h2 := Over.w (η[(Over.pullback f₂).obj X])
    have h1 := Over.w (η[(Over.pullback f₁).obj X])
    erw [← Category.assoc, h2, h1]
    simp

end TwistDescentXC

end TwistDescentXC
