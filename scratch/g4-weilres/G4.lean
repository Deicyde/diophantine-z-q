import Mathlib
import ZInQKernel.HDecomp.B3Unram.B3b
import ZInQKernel.HDecomp.Repo.TorsionFree
import ZInQKernel.HDecomp.Repo.Numerics
import ZInQKernel.HDecomp.Descent.B3Assembly
import ZInQKernel.HDecomp.Objects

/-!
# g4-weilres: glue step G4 of `docs/research/h-decomposition.md` (Weil restriction, Hom field)

Report: `docs/research/g4-weilres.md`. Headline: `G4WeilRes.homField_of_model_leaves`.

Contents, in order:
* `G4Conj` (generic, any category with pullbacks): the comparison `cmp` between base changes
  along `f₂ = s ≫ f₁` respects multiplication and unit; the conjugate `conj` of a morphism; the
  conjugate of a monoid homomorphism is one (`conj_isMonHom`); multiplicativity, functoriality.
* The bridge `GalUnramifiedOutside L T ↔ ∀ p ∉ T, UnramifiedAt L p` for finite Galois `L ⊆ ℚ̄`
  (`galUnramifiedOutside_iff`; the new direction via Mathlib's profinite transitivity and
  `Ideal.Quotient.stabilizerHom_surjective_of_profinite`, as in glue-b3b's `exists_inertia_neg`).
* The Hom-field core (`homField_core`: Minkowski + infinite Galois theory) and its numerical form
  (`homField_le_heightD`).
* The Hom lattice of a finite family of abelian varieties over `ℚ̄`, its rank (leaf
  `PkgI3.HomFreeFinite`), its `ℓ`-adic faithfulness.
* The conjugates of a model `A/K` (`conjData`) and the conjugation action of `G_ℚ` on their Hom
  lattice (`conjAction`, `conjActionExists`): the Weil-restriction step, constructed.
* Continuity from EGA IV₃ 8.8.2 (`MorphismsDescend` → `conjAction_continuous`), inertia from good
  reduction (`InertiaFixesHoms` → `conjAction_inertia`), the headline, and the consumers
  (`b3_of_homField` for G7, `cm_degree_of_homField` for the CM branch).

Inputs are `def … : Prop` hypotheses; no `sorry`, no `axiom`.
-/

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

namespace G4WeilRes

open GlueB3Unram GlueDescent.B2Q NumberField
open scoped Pointwise

/-! ## Places over `p` exist -/

/-- There is a valuation subring of `ℚ̄` over every prime `p`. -/
theorem exists_liesOver (p : ℕ) (hp : p.Prime) : ∃ w : ValuationSubring Qbar, LiesOver w p := by
  let A : Subring Qbar := ⊥
  let pA : A := ⟨(p : Qbar), by simpa using (⊥ : Subring Qbar).natCast_mem p⟩
  let I : Ideal A := Ideal.span {pA}
  have hI : I ≠ ⊤ := by
    intro h
    have h1 : (1 : A) ∈ I := by rw [h]; trivial
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h1
    obtain ⟨n, hn⟩ := Subring.mem_bot.mp a.2
    have h2 : ((n * p : ℤ) : Qbar) = ((1 : ℤ) : Qbar) := by
      have := congrArg Subtype.val ha
      simp only [Subring.coe_mul, OneMemClass.coe_one] at this
      push_cast
      rw [hn]; exact this
    have h3 : n * (p : ℤ) = 1 := Int.cast_injective h2
    have h4 : (p : ℤ) ∣ 1 := ⟨n, by rw [← h3]; ring⟩
    have := Int.eq_one_of_dvd_one (by positivity) h4
    exact hp.one_lt.ne' (by exact_mod_cast this)
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  refine ⟨B, ?_⟩
  have hmem : (p : Qbar) ∈ B.nonunits := hB ⟨pA, Ideal.subset_span rfl, rfl⟩
  exact (ValuationSubring.mem_nonunits_iff B).mp hmem

/-! ## A Galois automorphism maps a normal subfield into itself -/

theorem map_mem_of_normal (L : IntermediateField ℚ Qbar) [Normal ℚ L] (σ : Gal) {y : Qbar}
    (hy : y ∈ L) : σ y ∈ L := by
  have h := AlgEquiv.restrictNormal_commutes σ L ⟨y, hy⟩
  rw [← show algebraMap L Qbar ⟨y, hy⟩ = y from rfl, ← h]
  exact (AlgEquiv.restrictNormal σ L ⟨y, hy⟩).2

/-! ## Lifting a residually trivial automorphism of `L` into an inertia group -/

/-- `σ` acts trivially modulo `w` on the algebraic integers of `L`. -/
def ResTrivOn (L : IntermediateField ℚ Qbar) (w : ValuationSubring Qbar) (σ : Gal) : Prop :=
  ∀ y : Qbar, IsIntegral ℤ y → y ∈ L → w.valuation (σ y - y) < 1

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **The inertia lift.** Let `L ⊆ ℚ̄` be finite Galois, `w` a place over `p` and `σ ∈ G_ℚ`
acting trivially modulo `w` on the algebraic integers of `L`. Then some `s ∈ I_w` agrees with
`σ` on `L`. -/
theorem exists_inertia_restrict (L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ L]
    [IsGalois ℚ L] (p : ℕ) (hp : p.Prime) (w : ValuationSubring Qbar) (hw : LiesOver w p)
    (σ : Gal) (hσ : ResTrivOn L w σ) :
    ∃ s : Gal, s ∈ inertiaGQ w ∧ ∀ y ∈ L, s y = σ y := by
  classical
  let H : Subgroup Gal := L.fixingSubgroup
  have hH : ∀ g : Gal, g ∈ H ↔ ∀ y ∈ L, g y = y := fun g =>
    IntermediateField.mem_fixingSubgroup_iff L g
  have hHopen : IsOpen (H : Set Gal) := IntermediateField.fixingSubgroup_isOpen L
  have hHclosed : IsClosed (H : Set Gal) := Subgroup.isClosed_of_isOpen H hHopen
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hHclosed.isCompact
  let A := FixedPoints.subalgebra ℤ B H
  let Q := centerIdeal w
  haveI : SMulCommClass H A B := ⟨fun h a b => by
    rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, smul_mul', a.2 h]⟩
  -- elements of `A` lie in `L`
  have hAL : ∀ a : A, ((a : B) : Qbar) ∈ L := by
    intro a
    rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
    intro g hg
    have := a.2 ⟨g, hg⟩
    exact congrArg Subtype.val this
  have hAint : ∀ a : A, IsIntegral ℤ ((a : B) : Qbar) := fun a =>
    (mem_integralClosure_iff ℤ Qbar).mp (a : B).2
  -- the valuation input on `A`
  have hAval : ∀ (a : A) (τ : Gal), ResTrivOn L w τ →
      w.valuation (((a : B) : Qbar) - τ ((a : B) : Qbar)) < 1 := by
    intro a τ hτ
    rw [Valuation.map_sub_swap]
    exact hτ _ (hAint a) (hAL a)
  -- `σ⁻¹` is also residually trivial on `L`
  have hσi : ResTrivOn L w σ⁻¹ := by
    intro y hy hyL
    have hy' : IsIntegral ℤ ((σ⁻¹ : Gal) y) := hy.map ((σ⁻¹ : Gal) : Qbar →+* Qbar).toIntAlgHom
    have h := hσ _ hy' (map_mem_of_normal L σ⁻¹ hyL)
    have hss : σ ((σ⁻¹ : Gal) y) = y := by
      show (σ * σ⁻¹) y = y
      rw [mul_inv_cancel]; rfl
    rw [hss, Valuation.map_sub_swap] at h
    exact h
  -- step 1: `σ • Q` and `Q` lie over the same prime of `A`
  have hunder : (σ • Q).under A = Q.under A := by
    ext a
    rw [Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_centerIdeal, mem_centerIdeal]
    have h := hAval a σ⁻¹ hσi
    show w.valuation ((σ⁻¹ : Gal) ((a : B) : Qbar)) < 1 ↔ w.valuation ((a : B) : Qbar) < 1
    constructor
    · intro h1
      have : ((a : B) : Qbar) = (((a : B) : Qbar) - (σ⁻¹ : Gal) ((a : B) : Qbar)) +
          (σ⁻¹ : Gal) ((a : B) : Qbar) := by ring
      rw [this]; exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt h h1)
    · intro h1
      have : (σ⁻¹ : Gal) ((a : B) : Qbar) = ((a : B) : Qbar) -
          (((a : B) : Qbar) - (σ⁻¹ : Gal) ((a : B) : Qbar)) := by ring
      rw [this]; exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h1 h)
  -- step 2: transitivity over `A` gives `τ` stabilizing `Q` and agreeing with `σ` on `L`
  haveI hσQ : (σ • Q).IsPrime := by
    show (σ • centerIdeal w).IsPrime
    rw [← centerIdeal_smul]; infer_instance
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := A) (G := H)
    (σ • Q) Q hunder
  let τ : Gal := (g : Gal) * σ
  have hτQ : τ • Q = Q := by
    show ((g : Gal) * σ) • Q = Q
    rw [mul_smul]; exact hg.symm
  have hτL : ∀ y ∈ L, τ y = σ y := by
    intro y hy
    show (g : Gal) (σ y) = σ y
    exact (hH g).mp g.2 _ (map_mem_of_normal L σ hy)
  have hτ : ResTrivOn L w τ := by
    intro y hy hyL
    rw [hτL y hyL]; exact hσ y hy hyL
  -- step 3: `τ` induces an `A/P`-automorphism of `B/Q`
  let f : B ≃+* B := MulSemiringAction.toRingEquiv Gal B τ
  have hQf : Q = Q.map f := by
    ext b
    rw [Ideal.mem_map_of_equiv]
    constructor
    · intro hb
      refine ⟨τ⁻¹ • b, ?_, by simp [f]⟩
      rw [← Ideal.mem_pointwise_smul_iff_inv_smul_mem, hτQ]; exact hb
    · rintro ⟨x, hx, rfl⟩
      rw [← hτQ]
      exact Ideal.smul_mem_pointwise_smul_iff.mpr hx
  let e : (B ⧸ Q) ≃+* (B ⧸ Q) := Ideal.quotientEquiv Q Q f hQf
  have he : ∀ b : B, e (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q (τ • b) := fun b => rfl
  let φ : (B ⧸ Q) ≃ₐ[A ⧸ Q.under A] (B ⧸ Q) := AlgEquiv.ofRingEquiv (f := e) (by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver, he, Ideal.Quotient.eq, mem_centerIdeal]
    have h := hAval a τ hτ
    rw [Valuation.map_sub_swap] at h
    exact h)
  -- step 4: Mathlib's surjectivity gives `h' ∈ H` acting on `B/Q` as `τ`
  obtain ⟨h', hh'⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := H)
    (Q.under A) Q φ
  have hact : ∀ b : B, Ideal.Quotient.mk Q (((h' : H) : Gal) • b) =
      Ideal.Quotient.mk Q (τ • b) := by
    intro b
    have := congrArg (fun ψ => ψ (Ideal.Quotient.mk Q b)) hh'
    exact this
  let k : Gal := ((h' : H) : Gal)
  have hkQ : k • Q = Q := h'.2
  have hkL : ∀ y ∈ L, k y = y := (hH k).mp (h' : H).2
  let s : Gal := k⁻¹ * τ
  refine ⟨s, ?_, ?_⟩
  · apply mem_inertia_of_center hp hw s
    · show (k⁻¹ * τ) • Q = Q
      rw [mul_smul, hτQ, inv_smul_eq_iff, hkQ]
    · intro b
      have h1 := hact (s • b)
      have h2 : ((h' : H) : Gal) • (s • b) = τ • b := by
        show k • ((k⁻¹ * τ) • b) = τ • b
        rw [mul_smul, smul_inv_smul]
      rw [h2, Ideal.Quotient.eq] at h1
      have h3 : b - s • b ∈ Q := by
        have h4 : τ • (b - s • b) ∈ τ • Q := by rw [hτQ, smul_sub]; exact h1
        rwa [Ideal.smul_mem_pointwise_smul_iff] at h4
      have := Q.neg_mem h3
      rwa [neg_sub] at this
  · intro y hy
    show k⁻¹ (τ y) = σ y
    rw [hτL y hy]
    have hk' : k⁻¹ ∈ H := H.inv_mem (h' : H).2
    exact (hH _).mp hk' _ (map_mem_of_normal L σ hy)

/-! ## The bridge -/

/-- `P.under ℤ = (p)` for a prime of `𝓞 L` containing the prime `p`. -/
theorem under_eq_span {L : IntermediateField ℚ Qbar} [NumberField L] (p : ℕ) (hp : p.Prime)
    (P : Ideal (𝓞 L)) [P.IsPrime] (hpP : ((p : ℤ) : 𝓞 L) ∈ P) :
    P.under ℤ = Ideal.span {(p : ℤ)} := by
  have : Fact p.Prime := ⟨hp⟩
  have hmem : (p : ℤ) ∈ P.under ℤ := by
    rw [Ideal.under, Ideal.mem_comap]; simpa using hpP
  have hle : Ideal.span {(p : ℤ)} ≤ P.under ℤ :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
  exact ((Int.ideal_span_isMaximal_of_prime p).eq_of_le
    (Ideal.comap_isPrime (algebraMap ℤ (𝓞 L)) P).ne_top hle).symm

/-- **Bridge (glue, proved).** If every inertia group of `G_ℚ` over `p` fixes the finite Galois
field `L ⊆ ℚ̄`, then `L` is unramified at `p` in glue-descent's ideal-theoretic sense. -/
theorem unramifiedAt_of_inertia_le (L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ L]
    [IsGalois ℚ L] (p : ℕ) (hp : p.Prime)
    (h : ∀ w : ValuationSubring Qbar, LiesOver w p → inertiaGQ w ≤ L.fixingSubgroup) :
    UnramifiedAt L p := by
  haveI : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  intro P hP hpP
  obtain ⟨w, hw⟩ := exists_liesOver p hp
  let P₀ : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal w).comap (embW L w)
  haveI hP₀prime : P₀.IsPrime := Ideal.comap_isPrime _ _
  have hpP₀ : ((p : ℤ) : 𝓞 L) ∈ P₀ := by
    show embW L w ((p : ℤ) : 𝓞 L) ∈ IsLocalRing.maximalIdeal w
    rw [ValuationSubring.valuation_lt_one_iff]
    have : ((embW L w ((p : ℤ) : 𝓞 L) : w) : Qbar) = (p : Qbar) := by
      simp [embW, emb]
    rw [this]; exact hw
  let G := L ≃ₐ[ℚ] L
  have hunder : P.under ℤ = P₀.under ℤ := by
    rw [under_eq_span p hp P hpP, under_eq_span p hp P₀ hpP₀]
  -- the inertia group of `P₀` in `Gal(L/ℚ)` is trivial
  have htriv : ∀ g ∈ P₀.inertia G, g = 1 := by
    intro g hg
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (E := Qbar) (K₁ := L) g
    have hσL : ∀ x : L, algebraMap L Qbar (g x) = σ (algebraMap L Qbar x) := by
      intro x
      rw [← hσ]; exact AlgEquiv.restrictNormal_commutes σ L x
    have hres : ResTrivOn L w σ := by
      intro y hy hyL
      let x : 𝓞 L := ⟨⟨y, hyL⟩, by
        rw [mem_integralClosure_iff]
        exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ L Qbar)
          (algebraMap L Qbar).injective).mp hy⟩
      have hx := (Ideal.mem_inertia.mp hg) x
      change embW L w (g • x - x) ∈ IsLocalRing.maximalIdeal w at hx
      rw [ValuationSubring.valuation_lt_one_iff] at hx
      have he1 : ((embW L w (g • x - x) : w) : Qbar) = emb L (g • x) - emb L x := by
        show emb L (g • x - x) = _
        rw [map_sub]
      have he2 : emb L (g • x) = σ y := by
        simp only [emb, RingHom.comp_apply]
        rw [show σ y = σ (algebraMap L Qbar ⟨y, hyL⟩) from rfl, ← hσL]
        rfl
      have he : ((embW L w (g • x - x) : w) : Qbar) = σ y - y := by
        rw [he1, he2]; rfl
      rw [he] at hx; exact hx
    obtain ⟨s, hs, hsL⟩ := exists_inertia_restrict L p hp w hw σ hres
    have hsfix := (IntermediateField.mem_fixingSubgroup_iff L s).mp (h w hw hs)
    apply AlgEquiv.ext
    intro x
    apply (algebraMap L Qbar).injective
    rw [hσL x]
    show σ (x : Qbar) = (x : Qbar)
    rw [← hsL _ x.2, hsfix _ x.2]
  have hcard : Nat.card (P₀.inertia G) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ((htriv a a.2).trans (htriv b b.2).symm)⟩, ⟨1⟩⟩
  have e₀ : P₀.ramificationIdx ℤ = 1 := by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (P₀.under ℤ) P₀ G,
      ← Ideal.card_inertia_eq_ramificationIdxIn (G := G) (P₀.under ℤ) P₀, hcard]
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (P.under ℤ) P G, hunder,
    Ideal.ramificationIdxIn_eq_ramificationIdx (P₀.under ℤ) P₀ G, e₀]

/-- The Galois form of "unramified outside `T`" gives glue-descent's form at every `p ∉ T`. -/
theorem unramifiedAt_of_galUnramifiedOutside (L : IntermediateField ℚ Qbar)
    [FiniteDimensional ℚ L] [IsGalois ℚ L] (T : Finset ℕ) (h : GalUnramifiedOutside L T) :
    ∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p :=
  fun p hpT => unramifiedAt_of_inertia_le L p p.2 (fun w hw => h p p.2 hpT w hw)

/-- And conversely (glue-b3-unram's bridge): the two forms agree on finite Galois fields. -/
theorem galUnramifiedOutside_iff (L : IntermediateField ℚ Qbar)
    [FiniteDimensional ℚ L] [IsGalois ℚ L] (T : Finset ℕ) :
    GalUnramifiedOutside L T ↔ ∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p :=
  ⟨unramifiedAt_of_galUnramifiedOutside L T, fun h p hp hpT w hw =>
    inertia_le_of_unramifiedAt L p hp (h ⟨p, hp⟩ hpT) w hw⟩


/-! ## The Hom field: the core theorem (Minkowski + infinite Galois theory + the bridge)

N5 L544-563, with the Weil restriction `W₀ = Res_{K/ℚ} A` replaced by what the argument uses of
it: a free `ℤ`-module `M` of rank `r` (the geometric endomorphism lattice of `W₀`, i.e. the direct
sum of the Hom groups among the conjugates of `A`) with a `ℤ`-linear action of `G_ℚ` that is
continuous (every element has an open stabilizer: each geometric homomorphism is defined over a
number field) and on which every inertia group over a prime `p ∉ T` acts trivially. -/

section Core

variable {M : Type*} [AddCommGroup M]

/-- The `GL_r(ℤ)`-realization of the automorphisms of a free `ℤ`-module with a basis. -/
noncomputable def toGL {r : ℕ} (b : Module.Basis (Fin r) ℤ M) :
    (M ≃ₗ[ℤ] M) →* Matrix.GeneralLinearGroup (Fin r) ℤ :=
  (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp
    (LinearMap.GeneralLinearGroup.generalLinearEquiv ℤ M).symm.toMonoidHom

theorem toGL_injective {r : ℕ} (b : Module.Basis (Fin r) ℤ M) :
    Function.Injective (toGL b) := by
  intro f g h
  have h1 := congrArg (fun u : Matrix.GeneralLinearGroup (Fin r) ℤ =>
    (u : Matrix (Fin r) (Fin r) ℤ)) h
  have h2 : (f : M →ₗ[ℤ] M) = g := (LinearMap.toMatrixAlgEquiv b).injective h1
  exact LinearEquiv.toLinearMap_injective h2

theorem toGL_eq_one_iff {r : ℕ} (b : Module.Basis (Fin r) ℤ M) (f : M ≃ₗ[ℤ] M) :
    toGL b f = 1 ↔ f = 1 :=
  ⟨fun h => toGL_injective b (h.trans (map_one _).symm), fun h => by rw [h, map_one]⟩

/-- An automorphism is the identity iff it fixes a basis. -/
theorem eq_one_iff_basis {ι : Type*} (b : Module.Basis ι ℤ M) (f : M ≃ₗ[ℤ] M) :
    f = 1 ↔ ∀ i, f (b i) = b i := by
  constructor
  · intro h i; rw [h]; rfl
  · intro h
    apply LinearEquiv.toLinearMap_injective
    apply b.ext
    intro i
    simpa using h i

/-- **G4, the Hom field (core, proved).** Let `K ⊆ ℚ̄` be finite Galois, unramified outside `T`
(Galois form), and let `G_ℚ` act `ℤ`-linearly on a free `ℤ`-module `M` with basis indexed by
`Fin r`, continuously (open stabilizers), with every inertia group over every prime `p ∉ T`
acting trivially. Then there is a finite Galois `L ⊇ K` such that `G_L` acts trivially on `M`
(`L` defines every element of `M`), `[L:ℚ] ≤ [K:ℚ]·3^{r²}` (Minkowski), and `L` is unramified
outside `T`, in both the Galois form and glue-descent's ideal-theoretic form. -/
theorem homField_core (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    {r : ℕ} (b : Module.Basis (Fin r) ℤ M) (ρ : Gal →* (M ≃ₗ[ℤ] M))
    (hcont : ∀ m : M, IsOpen {σ : Gal | ρ σ m = m})
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hinert : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, ρ s = 1) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, ρ σ = 1) ∧
      Module.finrank ℚ L ≤ Module.finrank ℚ K * 3 ^ (r ^ 2) ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) := by
  classical
  let ρ' : Gal →* Matrix.GeneralLinearGroup (Fin r) ℤ := (toGL b).comp ρ
  have hker : ρ'.ker = ρ.ker := by
    ext σ
    simp only [MonoidHom.mem_ker]
    exact toGL_eq_one_iff b (ρ σ)
  -- the kernel is open
  have hset : (ρ.ker : Set Gal) = ⋂ i, {σ : Gal | ρ σ (b i) = b i} := by
    ext σ
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_ofPred_eq]
    exact eq_one_iff_basis b (ρ σ)
  have hNopen : IsOpen (ρ.ker : Set Gal) := by
    rw [hset]; exact isOpen_iInter_of_finite fun i => hcont (b i)
  have hNclosed : IsClosed (ρ.ker : Set Gal) := Subgroup.isClosed_of_isOpen _ hNopen
  let NC : ClosedSubgroup Gal := { toSubgroup := ρ.ker, isClosed' := hNclosed }
  let E : IntermediateField ℚ Qbar := IntermediateField.fixedField NC.toSubgroup
  have hE : E.fixingSubgroup = ρ.ker := InfiniteGalois.fixingSubgroup_fixedField NC
  haveI hEfd : FiniteDimensional ℚ E :=
    (InfiniteGalois.isOpen_iff_finite E).mp (by
      show IsOpen (E.fixingSubgroup : Set Gal)
      rw [hE]; exact hNopen)
  haveI hEgal : IsGalois ℚ E :=
    (InfiniteGalois.normal_iff_isGalois E).mp (by rw [hE]; exact ρ.normal_ker)
  -- `[E:ℚ] = |ρ(G_ℚ)| ≤ 3^{r²}`
  have hcardE : Module.finrank ℚ E = Nat.card ρ'.range := by
    rw [← IsGalois.card_aut_eq_finrank]
    have e1 := QuotientGroup.quotientKerEquivOfSurjective (AlgEquiv.restrictNormalHom (F := ℚ)
      (K₁ := Qbar) E) (AlgEquiv.restrictNormalHom_surjective (E := Qbar))
    have e2 := QuotientGroup.quotientKerEquivRange ρ'
    have c1 : Nat.card (E ≃ₐ[ℚ] E) =
        (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) E).ker.index :=
      (Nat.card_congr e1.toEquiv).symm
    have c2 : Nat.card ρ'.range = ρ'.ker.index := (Nat.card_congr e2.toEquiv).symm
    rw [c1, c2, IntermediateField.restrictNormalHom_ker, hE, hker]
  haveI : Finite ρ'.range := by
    apply Nat.finite_of_card_ne_zero
    rw [← hcardE]; exact Module.finrank_pos.ne'
  have hE3 : Module.finrank ℚ E ≤ 3 ^ (r ^ 2) := by
    rw [hcardE]; exact GlueRepo.TorsionFree.card_le_three_pow ρ'.range
  -- `L = E ⊔ K`
  refine ⟨E ⊔ K, inferInstance, inferInstance, le_sup_right, ?_, ?_, ?_, ?_⟩
  · intro σ hσ
    have h1 : σ ∈ E.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_left hσ
    rw [hE] at h1
    exact h1
  · calc Module.finrank ℚ ↥(E ⊔ K) ≤ Module.finrank ℚ E * Module.finrank ℚ K :=
          IntermediateField.finrank_sup_le E K
      _ ≤ 3 ^ (r ^ 2) * Module.finrank ℚ K := Nat.mul_le_mul_right _ hE3
      _ = Module.finrank ℚ K * 3 ^ (r ^ 2) := Nat.mul_comm _ _
  · have hgal : GalUnramifiedOutside (E ⊔ K) T := by
      intro p hp hpT w hw s hs
      rw [IntermediateField.fixingSubgroup_sup]
      refine ⟨?_, hK p hp hpT w hw hs⟩
      rw [hE]
      exact hinert p hp hpT w hw s hs
    exact hgal
  · apply unramifiedAt_of_galUnramifiedOutside
    intro p hp hpT w hw s hs
    rw [IntermediateField.fixingSubgroup_sup]
    refine ⟨?_, hK p hp hpT w hw hs⟩
    rw [hE]
    exact hinert p hp hpT w hw s hs

/-- **G4 with the manuscript's numbers.** If `[K:ℚ] ≤ F₀ = 324!` and `r ≤ 16F₀²` (N5 L547-548),
the Hom field has `[L:ℚ] ≤ D = F₀·3^{256F₀⁴}` (`ZInQ.heightD`). -/
theorem homField_le_heightD (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0)
    {r : ℕ} (hr : r ≤ 16 * ZInQ.heightF0 ^ 2) (b : Module.Basis (Fin r) ℤ M)
    (ρ : Gal →* (M ≃ₗ[ℤ] M))
    (hcont : ∀ m : M, IsOpen {σ : Gal | ρ σ m = m})
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hinert : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, ρ s = 1) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, ρ σ = 1) ∧
      Module.finrank ℚ L ≤ ZInQ.heightD ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) := by
  obtain ⟨L, h1, h2, hKL, hdef, hdeg, hgal, hram⟩ := homField_core K b ρ hcont T hK hinert
  refine ⟨L, h1, h2, hKL, hdef, ?_, hgal, hram⟩
  exact hdeg.trans (GlueRepo.Numerics.a8_degree ZInQ.Compiler.Precision.heightD_eq hKF le_rfl hr)

end Core


/-! ## The lattice of the conjugates: rank, faithfulness, and the abelian-variety instantiation

The manuscript's `End(W₀_ℚ̄) = ⊕_{σ,τ} Hom(σA, τA)`: here the direct sum over ordered pairs of
`n` abelian varieties over `ℚ̄` (the conjugates of `A`, `n ≤ [K:ℚ] ≤ F₀`), as a product of
`PkgI3.AbVar.Hom` groups. -/

section Lattice

/-- **Rank of the lattice (glue, proved).** A product over ordered pairs `(i, j) ∈ n × n` of free
finite `ℤ`-modules of rank `≤ c` is free and finite of rank `≤ c·n²`. -/
theorem pi_rank_le {ι : Type*} [Fintype ι] {c : ℕ} (H : ι × ι → Type*) [∀ ij, AddCommGroup (H ij)]
    [∀ ij, Module.Free ℤ (H ij)] [∀ ij, Module.Finite ℤ (H ij)]
    (hH : ∀ ij, Module.finrank ℤ (H ij) ≤ c) :
    Module.finrank ℤ (∀ ij, H ij) ≤ c * Fintype.card ι ^ 2 := by
  rw [Module.finrank_pi_fintype]
  calc ∑ ij, Module.finrank ℤ (H ij) ≤ ∑ _ij : ι × ι, c :=
        Finset.sum_le_sum fun ij _ => hH ij
    _ = c * Fintype.card ι ^ 2 := by simp [Fintype.card_prod, sq, mul_comm]

/-- **Inertia acts trivially on the lattice (glue, proved; N5 L559-561).** If the lattice `M`
embeds equivariantly and injectively into a module `N` (in the application: `ℓ`-adic
realization, `Hom(σA, τA) → Hom_{ℤ_ℓ}(T_ℓ σA, T_ℓ τA)`, injective by Mumford §19 Thm 3, the leaf
`PkgI3.HomFreeFinite`), then every `s` acting trivially on `N` (in the application: inertia at
`p ∉ T`, by Néron–Ogg–Shafarevich, the leaf `PkgI2.NeronOggShafarevich`) acts trivially on `M`. -/
theorem trivial_of_faithful {G M N : Type*} [Group G] [AddCommGroup M] [AddCommGroup N]
    (ρ : G →* (M ≃ₗ[ℤ] M)) (τ : G →* (N ≃ₗ[ℤ] N)) (ι : M →+ N) (hι : Function.Injective ι)
    (heq : ∀ g m, ι (ρ g m) = τ g (ι m)) (s : G) (hs : τ s = 1) : ρ s = 1 := by
  apply LinearEquiv.ext
  intro m
  apply hι
  rw [heq, hs]
  rfl

/-- The `ℓ`-adic side: if `s` acts trivially on the Tate modules `T i`, it acts trivially on
`Hom_{ℤ_ℓ}(T i, T j)` by conjugation. -/
theorem conj_trivial {R : Type*} [CommRing R] {T₁ T₂ : Type*} [AddCommGroup T₁] [Module R T₁]
    [AddCommGroup T₂] [Module R T₂] (a₁ : T₁ ≃ₗ[R] T₁) (a₂ : T₂ ≃ₗ[R] T₂) (h₁ : a₁ = 1)
    (h₂ : a₂ = 1) (φ : T₁ →ₗ[R] T₂) :
    (a₂ : T₂ →ₗ[R] T₂) ∘ₗ φ ∘ₗ (a₁.symm : T₁ →ₗ[R] T₁) = φ := by
  subst h₁; subst h₂; rfl

open PkgI3 PkgI3.AbVar CategoryTheory MonObj

/-- The geometric Hom lattice of `n` abelian varieties over `ℚ̄`: `⊕_{(i,j)} Hom(A i, A j)`. -/
abbrev HomLattice {Idx : Type} (A : Idx → AbVar Qbar) : Type :=
  ∀ ij : Idx × Idx, AbVar.Hom (A ij.1) (A ij.2)

/-- **Mumford's bound on the lattice (from the leaf `HomFreeFinite`).** For abelian surfaces
`A i` over `ℚ̄`, the lattice `⊕ Hom(A i, A j)` is free and finite of rank `≤ 16n²`. -/
theorem homLattice_free (hHFF : HomFreeFinite) {Idx : Type} [Fintype Idx] (A : Idx → AbVar Qbar)
    (hdim : ∀ i, (A i).dim = 2) :
    Module.Free ℤ (HomLattice A) ∧ Module.Finite ℤ (HomLattice A) ∧
      Module.finrank ℤ (HomLattice A) ≤ 16 * Fintype.card Idx ^ 2 := by
  haveI : ∀ ij : Idx × Idx, Module.Free ℤ (AbVar.Hom (A ij.1) (A ij.2)) :=
    fun ij => (hHFF Qbar (A ij.1) (A ij.2)).1
  haveI : ∀ ij : Idx × Idx, Module.Finite ℤ (AbVar.Hom (A ij.1) (A ij.2)) :=
    fun ij => (hHFF Qbar (A ij.1) (A ij.2)).2.1
  refine ⟨inferInstance, inferInstance, pi_rank_le _ fun ij => ?_⟩
  have h := (hHFF Qbar (A ij.1) (A ij.2)).2.2.1
  rw [hdim, hdim] at h
  have h16 : ((Module.finrank ℤ (AbVar.Hom (A ij.1) (A ij.2)) : ℕ∞) : WithBot ℕ∞) ≤
      (((16 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    refine h.trans (le_of_eq ?_)
    rfl
  exact_mod_cast h16

/-- **The `ℓ`-adic realization is faithful (from the leaf `HomFreeFinite`).** `Hom(A, B) →
Hom_{ℤ_ℓ}(T_ℓ A, T_ℓ B)` is injective for `ℓ` invertible in `k`: `HomFreeFinite` gives
injectivity on `ℤ_ℓ ⊗ Hom(A, B)`, and `Hom(A, B) → ℤ_ℓ ⊗ Hom(A, B)` is injective because
`Hom(A, B)` is free (flat) and `ℤ → ℤ_ℓ` is injective. This is the `ι` of `trivial_of_faithful`
in the application (N5 L559-561). -/
theorem tateHom_injective (hHFF : HomFreeFinite) {k : Type} [Field k] (A B : AbVar k)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) : Function.Injective (tateHom ℓ A B) := by
  have hinj := (hHFF k A B).2.2.2 ℓ hℓ
  haveI : Module.Free ℤ (AbVar.Hom A B) := (hHFF k A B).1
  let j : AbVar.Hom A B →ₗ[ℤ] TensorProduct ℤ ℤ_[ℓ] (AbVar.Hom A B) :=
    ((Algebra.linearMap ℤ ℤ_[ℓ]).rTensor (AbVar.Hom A B)).comp
      (TensorProduct.lid ℤ (AbVar.Hom A B)).symm.toLinearMap
  have hj : Function.Injective j := by
    have h1 : Function.Injective (Algebra.linearMap ℤ ℤ_[ℓ]) := by
      intro a b hab
      exact Int.cast_injective hab
    exact (Module.Flat.rTensor_preserves_injective_linearMap _ h1).comp
      (TensorProduct.lid ℤ (AbVar.Hom A B)).symm.injective
  have hcomp : ∀ f, tateHomZl ℓ A B (j f) = tateHom ℓ A B f := by
    intro f
    have hjf : j f = (1 : ℤ_[ℓ]) ⊗ₜ[ℤ] f := by
      show (Algebra.linearMap ℤ ℤ_[ℓ]).rTensor (AbVar.Hom A B)
        ((TensorProduct.lid ℤ (AbVar.Hom A B)).symm f) = _
      erw [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul]
      congr 1
    rw [hjf]
    exact (TensorProduct.lift.tmul _ _).trans (one_smul _ _)
  intro f g hfg
  apply hj
  apply hinj
  rw [hcomp, hcomp]
  exact hfg


/-- The `ℓ`-adic realization of the lattice: `f ↦ (T_ℓ(f_{ij}))_{ij}`. -/
noncomputable def tateLattice (ℓ : ℕ) [Fact ℓ.Prime] {Idx : Type} (A : Idx → AbVar Qbar) :
    HomLattice A →+ (∀ ij : Idx × Idx, (A ij.1).T ℓ →ₗ[ℤ_[ℓ]] (A ij.2).T ℓ) :=
  Pi.addMonoidHom fun ij => (tateHom ℓ (A ij.1) (A ij.2)).comp (Pi.evalAddMonoidHom _ ij)

/-- The realization of the lattice is injective (leaf `HomFreeFinite`; `ℓ ≠ 0` in `ℚ̄`). -/
theorem tateLattice_injective (hHFF : HomFreeFinite) (ℓ : ℕ) [hℓ : Fact ℓ.Prime] {Idx : Type}
    (A : Idx → AbVar Qbar) : Function.Injective (tateLattice ℓ A) := by
  intro f g h
  funext ij
  have hne : (ℓ : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.out.ne_zero
  exact tateHom_injective hHFF (A ij.1) (A ij.2) ℓ hne (congrFun h ij)

/-- **The inertia hypothesis from the `ℓ`-adic side (glue, proved).** If `G_ℚ` acts on the
realization `∏ Hom_{ℤ_ℓ}(T_ℓ A_i, T_ℓ A_j)` compatibly with `ρ` (equivariance: open, needs the
action on points), and inertia over `p ∉ T` acts trivially there (Néron–Ogg–Shafarevich for the
conjugates, which have good reduction above `p ∉ T`, G3), then `hinert` of
`homField_of_conjugates` holds. -/
theorem inertia_of_tate (hHFF : HomFreeFinite) (ℓ : ℕ) [Fact ℓ.Prime] {Idx : Type}
    (A : Idx → AbVar Qbar) (ρ : Gal →* (HomLattice A ≃ₗ[ℤ] HomLattice A))
    (τ : Gal →* ((∀ ij : Idx × Idx, (A ij.1).T ℓ →ₗ[ℤ_[ℓ]] (A ij.2).T ℓ) ≃ₗ[ℤ]
      (∀ ij : Idx × Idx, (A ij.1).T ℓ →ₗ[ℤ_[ℓ]] (A ij.2).T ℓ)))
    (heq : ∀ σ m, tateLattice ℓ A (ρ σ m) = τ σ (tateLattice ℓ A m)) (T : Finset ℕ)
    (htate : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, τ s = 1) :
    ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, ρ s = 1 :=
  fun p hp hpT w hw s hs => trivial_of_faithful ρ τ (tateLattice ℓ A)
    (tateLattice_injective hHFF ℓ A) heq s (htate p hp hpT w hw s hs)


/-- **G4 on the abelian-variety layer.** Let `K ⊆ ℚ̄` be finite Galois with `[K:ℚ] ≤ F₀`,
unramified outside `T`; let `A 0, …, A (n-1)` be abelian surfaces over `ℚ̄` (the conjugates of
the fibre object, indexed by a finite type of size `≤ F₀`, e.g. the embeddings `K → ℚ̄`), and let `G_ℚ` act `ℤ`-linearly on `⊕ Hom(A i, A j)` (the conjugation
action; its construction is the open part of G4) continuously and with every inertia group over
`p ∉ T` acting trivially. Then the Hom field `L ⊇ K` exists: finite Galois, `[L:ℚ] ≤ D`, every
element of the lattice is fixed by `G_L`, and `L` is unramified outside `T` (both forms).
Leaf used: `PkgI3.HomFreeFinite` (Mumford §19 Thm 3). -/
theorem homField_of_conjugates (hHFF : HomFreeFinite)
    (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0)
    {Idx : Type} [Fintype Idx] (hn : Fintype.card Idx ≤ ZInQ.heightF0) (A : Idx → AbVar Qbar)
    (hdim : ∀ i, (A i).dim = 2)
    (ρ : Gal →* (HomLattice A ≃ₗ[ℤ] HomLattice A))
    (hcont : ∀ m : HomLattice A, IsOpen {σ : Gal | ρ σ m = m})
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hinert : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, ρ s = 1) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, ρ σ = 1) ∧
      Module.finrank ℚ L ≤ ZInQ.heightD ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) := by
  obtain ⟨hfree, hfin, hrank⟩ := homLattice_free hHFF A hdim
  have hr : Module.finrank ℤ (HomLattice A) ≤ 16 * ZInQ.heightF0 ^ 2 :=
    hrank.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 2))
  exact homField_le_heightD K hKF hr (Module.finBasisOfFinrankEq ℤ (HomLattice A) rfl) ρ hcont T
    hK hinert

/-! ### The conjugation action

For `σ ∈ G_ℚ`, a conjugate of an abelian variety `X` over `ℚ̄` is an `X'` with a pullback square
`X' → X` over `Spec σ : Spec ℚ̄ → Spec ℚ̄` (the relation used by leaf-qm-fp's `IsBaseChangeOf`).
`ConjData` records a finite family closed under conjugation: `A i` is the `σ`-conjugate of
`A (σ⁻¹·i)` through `g σ i : A i → A (σ⁻¹·i)`. `IsConjAction D ρ` says that `ρ σ` sends
`f : A (σ⁻¹·i) → A (σ⁻¹·j)` to its conjugate `σf : A i → A j`, the morphism with
`g σ j ∘ σf = f ∘ g σ i`. Such a `ρ` is unique (`isConjAction_unique`), and for the conjugates of
a model `A/K` it exists (`conjAction`, `conjActionExists`). -/

open AlgebraicGeometry

/-- `Spec σ : Spec ℚ̄ → Spec ℚ̄`. -/
noncomputable abbrev specGal (σ : Gal) :
    Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of Qbar) :=
  Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar))

theorem specGal_mul (σ τ : Gal) : specGal (σ * τ) = specGal σ ≫ specGal τ := by
  rw [specGal, specGal, specGal, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem specGal_one : specGal 1 = 𝟙 _ := by
  rw [specGal, show CommRingCat.ofHom ((1 : Gal) : Qbar →+* Qbar) = 𝟙 _ from by ext; rfl]
  exact Spec.map_id _

/-- Conjugation data for a finite family of abelian varieties over `ℚ̄`: a permutation action of
`G_ℚ` on the indices and, for every `σ` and `i`, a pullback square exhibiting `A i` as the base
change of `A (σ⁻¹·i)` along `Spec σ`. -/
structure ConjData (Idx : Type) where
  A : Idx → AbVar Qbar
  act : Gal → Equiv.Perm Idx
  g : ∀ (σ : Gal) (i : Idx), (A i).X.left ⟶ (A ((act σ).symm i)).X.left
  pb : ∀ (σ : Gal) (i : Idx),
    IsPullback (g σ i) (A i).X.hom (A ((act σ).symm i)).X.hom (specGal σ)

/-- `ρ` is the conjugation action for the data `D`. -/
def IsConjAction {Idx : Type} (D : ConjData Idx)
    (ρ : Gal → HomLattice D.A → HomLattice D.A) : Prop :=
  ∀ (σ : Gal) (f : HomLattice D.A) (i j : Idx),
    (ρ σ f (i, j)).hom.left ≫ D.g σ j =
      D.g σ i ≫ (f ((D.act σ).symm i, (D.act σ).symm j)).hom.left

/-- **The conjugation action is unique (glue, proved).** -/
theorem isConjAction_unique {Idx : Type} (D : ConjData Idx)
    {ρ ρ' : Gal → HomLattice D.A → HomLattice D.A}
    (h : IsConjAction D ρ) (h' : IsConjAction D ρ') : ρ = ρ' := by
  funext σ f
  funext ij
  obtain ⟨i, j⟩ := ij
  apply AbVar.Hom.ext'
  apply CategoryTheory.Over.OverMorphism.ext
  apply (D.pb σ j).hom_ext
  · rw [h σ f i j, h' σ f i j]
  · rw [CategoryTheory.Over.w, CategoryTheory.Over.w]

/-- The conjugation action exists (proved below for the conjugates of a model, `conjActionExists`). -/
def ConjActionExists {Idx : Type} (D : ConjData Idx) : Prop :=
  ∃ ρ : Gal →* (HomLattice D.A ≃ₗ[ℤ] HomLattice D.A), IsConjAction D (fun σ f => ρ σ f)

/-! ### The conjugates of a model over a number field

For `A/K` with `K ⊆ ℚ̄` a number field, the conjugates are the base changes `A_e = A ×_{K,e} ℚ̄`
along the embeddings `e : K → ℚ̄`; `G_ℚ` permutes the embeddings, and the comparison maps
`G4Conj.cmp` give the squares `A_e → A_{σ⁻¹∘e}` over `Spec σ`. -/

/-- Base change of an abelian variety along a ring homomorphism `f : K → L` of fields
(as `PkgI3.AbVar.baseChange`, for an arbitrary embedding). -/
noncomputable def bcAlong {K L : Type} [Field K] [Field L] (A : AbVar K) (f : K →+* L) :
    AbVar L :=
  let F := CategoryTheory.Over.pullback (Spec.map (CommRingCat.ofHom f))
  letI : GrpObj (F.obj A.X) := Functor.grpObjObj
  haveI : IsProper (F.obj A.X).hom := by dsimp [F]; infer_instance
  haveI : Smooth (F.obj A.X).hom := by dsimp [F]; infer_instance
  haveI : GeometricallyIntegral (F.obj A.X).hom := by dsimp [F]; infer_instance
  { X := F.obj A.X }

variable (K : IntermediateField ℚ Qbar)

/-- `Spec e : Spec ℚ̄ → Spec K` for an embedding `e : K → ℚ̄`. -/
noncomputable abbrev specEmb (e : K →ₐ[ℚ] Qbar) :
    Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (e : K →+* Qbar))

/-- `G_ℚ` permutes the embeddings `K → ℚ̄`: `σ · e = σ ∘ e`. -/
noncomputable def embAct (σ : Gal) : Equiv.Perm (K →ₐ[ℚ] Qbar) where
  toFun e := (σ : Qbar →ₐ[ℚ] Qbar).comp e
  invFun e := ((σ⁻¹ : Gal) : Qbar →ₐ[ℚ] Qbar).comp e
  left_inv e := by
    ext x
    show (σ⁻¹ * σ) (e x) = e x
    rw [inv_mul_cancel]; rfl
  right_inv e := by
    ext x
    show (σ * σ⁻¹) (e x) = e x
    rw [mul_inv_cancel]; rfl

theorem specEmb_act (σ : Gal) (e : K →ₐ[ℚ] Qbar) :
    specEmb K (embAct K σ e) = specGal σ ≫ specEmb K e := by
  rw [specEmb, specEmb, specGal, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem specEmb_symm (σ : Gal) (e : K →ₐ[ℚ] Qbar) :
    specEmb K e = specGal σ ≫ specEmb K ((embAct K σ).symm e) :=
  (congrArg (specEmb K) ((embAct K σ).apply_symm_apply e)).symm.trans (specEmb_act K σ _)

/-- **The conjugation data of a model `A/K`** (constructed, no hypothesis): the `[K:ℚ]`
conjugates `A_e`, permuted by `G_ℚ`, with their pullback squares over `Spec σ`. -/
noncomputable def conjData (A : AbVar K) : ConjData (K →ₐ[ℚ] Qbar) where
  A e := bcAlong A (e : K →+* Qbar)
  act σ := embAct K σ
  g σ e := G4Conj.cmp A.X (specGal σ) (specEmb_symm K σ e)
  pb σ e := G4Conj.cmp_isPullback A.X (specGal σ) (specEmb_symm K σ e)

/-- There are `[K:ℚ]` conjugates. -/
theorem card_conjugates [FiniteDimensional ℚ K] :
    Fintype.card (K →ₐ[ℚ] Qbar) = Module.finrank ℚ K :=
  AlgHom.card ℚ K Qbar

section Action

open CategoryTheory MonObj

variable (A : AbVar K)

/-- Conjugation of one Hom group: `Hom(A_{σ⁻¹i}, A_{σ⁻¹j}) → Hom(A_i, A_j)`, additive
(`G4Conj.conj_mul`, `conj_one`), landing in homomorphisms (`G4Conj.conj_isMonHom`). -/
noncomputable def conjHom (σ : Gal) (i j : K →ₐ[ℚ] Qbar) :
    AbVar.Hom ((conjData K A).A ((embAct K σ).symm i)) ((conjData K A).A ((embAct K σ).symm j)) →+
      AbVar.Hom ((conjData K A).A i) ((conjData K A).A j) where
  toFun φ :=
    haveI hc : IsMonHom (show ((conjData K A).A i).X ⟶ ((conjData K A).A j).X from
        G4Conj.conj A.X A.X (specGal σ) (specEmb_symm K σ i) (specEmb_symm K σ j) φ.hom) :=
      G4Conj.conj_isMonHom' A.X A.X (specGal σ) (specEmb_symm K σ i) (specEmb_symm K σ j)
        φ.hom (show IsMonHom φ.hom from inferInstance)
    AbVar.Hom.mk' (show ((conjData K A).A i).X ⟶ ((conjData K A).A j).X from
      G4Conj.conj A.X A.X (specGal σ) (specEmb_symm K σ i) (specEmb_symm K σ j) φ.hom)
  map_zero' := AbVar.Hom.ext'
    (G4Conj.conj_one A.X A.X (specGal σ) (specEmb_symm K σ i) (specEmb_symm K σ j))
  map_add' φ ψ := AbVar.Hom.ext'
    (G4Conj.conj_mul A.X A.X (specGal σ) (specEmb_symm K σ i) (specEmb_symm K σ j) φ.hom ψ.hom)

theorem conjHom_hom (σ : Gal) (i j : K →ₐ[ℚ] Qbar) (φ) :
    (conjHom K A σ i j φ).hom =
      G4Conj.conj A.X A.X (specGal σ) (specEmb_symm K σ i) (specEmb_symm K σ j) φ.hom := rfl

/-- The action of `σ` on the lattice `⊕ Hom(A_i, A_j)`. -/
noncomputable def conjAct (σ : Gal) :
    HomLattice (conjData K A).A →+ HomLattice (conjData K A).A :=
  AddMonoidHom.pi fun ij => (conjHom K A σ ij.1 ij.2).comp
    (Pi.evalAddMonoidHom (fun ij : (K →ₐ[ℚ] Qbar) × (K →ₐ[ℚ] Qbar) =>
      AbVar.Hom ((conjData K A).A ij.1) ((conjData K A).A ij.2))
      ((embAct K σ).symm ij.1, (embAct K σ).symm ij.2))

theorem conjAct_apply (σ : Gal) (m : HomLattice (conjData K A).A) (i j : K →ₐ[ℚ] Qbar) :
    conjAct K A σ m (i, j) = conjHom K A σ i j (m ((embAct K σ).symm i, (embAct K σ).symm j)) :=
  rfl

theorem conjAct_isConjAction : IsConjAction (conjData K A) (fun σ m => conjAct K A σ m) := by
  intro σ m i j
  dsimp only
  rw [conjAct_apply, conjHom_hom]
  exact G4Conj.conj_cmp A.X A.X _ _ _ _

theorem conjAct_one (m : HomLattice (conjData K A).A) : conjAct K A 1 m = m := by
  funext ij
  obtain ⟨i, j⟩ := ij
  apply AbVar.Hom.ext'
  rw [conjAct_apply, conjHom_hom]
  exact G4Conj.conj_self A.X A.X (specGal 1) specGal_one _ _ _

theorem conjAct_mul (σ τ : Gal) (m : HomLattice (conjData K A).A) :
    conjAct K A (σ * τ) m = conjAct K A σ (conjAct K A τ m) := by
  funext ij
  obtain ⟨i, j⟩ := ij
  apply AbVar.Hom.ext'
  rw [conjAct_apply, conjAct_apply, conjHom_hom, conjHom_hom, conjAct_apply, conjHom_hom]
  have hi : specEmb K i = (specGal σ ≫ specGal τ) ≫
      specEmb K ((embAct K τ).symm ((embAct K σ).symm i)) := by
    rw [Category.assoc, ← specEmb_symm, ← specEmb_symm]
  have hj : specEmb K j = (specGal σ ≫ specGal τ) ≫
      specEmb K ((embAct K τ).symm ((embAct K σ).symm j)) := by
    rw [Category.assoc, ← specEmb_symm, ← specEmb_symm]
  exact (G4Conj.conj_congr A.X A.X (specGal (σ * τ)) _ _ (specGal_mul σ τ) hi hj _).trans
    (G4Conj.conj_comp A.X A.X (specGal τ) (specEmb_symm K τ _) (specEmb_symm K τ _)
      (specGal σ) (specEmb_symm K σ i) (specEmb_symm K σ j) hi hj _)

/-- **The conjugation action of `G_ℚ` on the Hom lattice of the conjugates (constructed).** -/
noncomputable def conjAction : Gal →* (HomLattice (conjData K A).A ≃ₗ[ℤ]
    HomLattice (conjData K A).A) where
  toFun σ := LinearEquiv.ofLinearMap (conjAct K A σ).toIntLinearMap
    (conjAct K A σ⁻¹).toIntLinearMap
    (LinearMap.ext fun m => by
      show conjAct K A σ (conjAct K A σ⁻¹ m) = m
      rw [← conjAct_mul, mul_inv_cancel, conjAct_one])
    (LinearMap.ext fun m => by
      show conjAct K A σ⁻¹ (conjAct K A σ m) = m
      rw [← conjAct_mul, inv_mul_cancel, conjAct_one])
  map_one' := LinearEquiv.ext fun m => conjAct_one K A m
  map_mul' σ τ := LinearEquiv.ext fun m => conjAct_mul K A σ τ m

theorem conjAction_apply (σ : Gal) (m : HomLattice (conjData K A).A) :
    conjAction K A σ m = conjAct K A σ m := rfl

/-- **The Weil-restriction step of G4 is glue, proved: the conjugation action exists.** -/
theorem conjActionExists : ConjActionExists (conjData K A) :=
  ⟨conjAction K A, conjAct_isConjAction K A⟩

end Action

/-- **G4 for a model `A/K` (the manuscript's statement, N5 L544-563).** Let `K ⊆ ℚ̄` be finite
Galois with `[K:ℚ] ≤ F₀`, unramified outside `T` (G2), and `A/K` an abelian surface whose
conjugates `A_e` are surfaces. Let `ρ = conjAction K A` be the conjugation action of `G_ℚ` on
`⊕_{e,e'} Hom(A_e, A_{e'})` (constructed; the unique action with `IsConjAction`). If `ρ` is
continuous and inertia outside `T` acts trivially, the Hom field `L ⊇ K` exists: finite Galois,
`[L:ℚ] ≤ D`, every geometric homomorphism among the conjugates is fixed by `G_L`, `L`
unramified outside `T` (both forms). Leaf: `PkgI3.HomFreeFinite`. -/
theorem homField_of_model (hHFF : HomFreeFinite) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0) (A : AbVar K)
    (hdim : ∀ e, ((conjData K A).A e).dim = 2)
    (hcont : ∀ m : HomLattice (conjData K A).A, IsOpen {σ : Gal | conjAction K A σ m = m})
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hinert : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, conjAction K A s = 1) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, conjAction K A σ = 1) ∧
      Module.finrank ℚ L ≤ ZInQ.heightD ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) :=
  homField_of_conjugates hHFF K hKF (by rw [card_conjugates]; exact hKF) (conjData K A).A hdim
    (conjAction K A) hcont T hK hinert

/-! ### Continuity of the conjugation action from the descent of morphisms

`HomDescends` is the input: a homomorphism between conjugates is fixed by conjugation through an
open subgroup of `G_ℚ`. It is a consequence of EGA IV₃ 8.8.2 (a morphism between base changes to
`ℚ̄ = colim L` of finitely presented `K`-schemes is the base change of a morphism over some number
field `L`; locator UNVERIFIED) together with the descent bookkeeping "conjugation by `σ ∈ G_L`
fixes a morphism defined over `L`" (`conj_unique` on the pasted squares `ℚ̄ → L → K`), which is
glue not formalized here. Stated as a `Prop` over the genuine objects (`PkgI3.AbVar`, Mathlib's
pullbacks, `G4Conj.conj`). -/

/-- **Input (EGA IV₃ 8.8.2 + descent bookkeeping; not formalized).** For abelian varieties
`A, B` over a number field `K ⊆ ℚ̄` and embeddings `e₁, e₂ : K → ℚ̄`, every morphism
`A ×_{K,e₁} ℚ̄ → B ×_{K,e₂} ℚ̄` over `ℚ̄` is fixed by the conjugation of an open subgroup of
`G_ℚ` (those `σ` fixing `e₁(K)`, `e₂(K)` and the field of definition). -/
def HomDescends : Prop :=
  ∀ (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] (A B : AbVar K)
    (e₁ e₂ : K →ₐ[ℚ] Qbar)
    (φ : (CategoryTheory.Over.pullback (specEmb K e₁)).obj A.X ⟶
      (CategoryTheory.Over.pullback (specEmb K e₂)).obj B.X),
    ∃ U : Subgroup Gal, IsOpen (U : Set Gal) ∧ ∀ σ ∈ U,
      ∀ (hf : specEmb K e₁ = specGal σ ≫ specEmb K e₁)
        (hg : specEmb K e₂ = specGal σ ≫ specEmb K e₂),
        G4Conj.conj A.X B.X (specGal σ) hf hg φ = φ

/-- `Spec ℚ̄ → Spec L` for a subfield `L ⊆ ℚ̄`. -/
noncomputable abbrev specIncl (L : IntermediateField ℚ Qbar) :
    Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of L) :=
  Spec.map (CommRingCat.ofHom (algebraMap L Qbar))

/-- `Spec e = Spec(ℚ̄ ← L) ≫ Spec e'` when `e = (L ↪ ℚ̄) ∘ e'`. -/
theorem specEmb_factor (L : IntermediateField ℚ Qbar) (e : K →ₐ[ℚ] Qbar) (e' : K →ₐ[ℚ] L)
    (he : ∀ x, (e' x : Qbar) = e x) :
    specEmb K e = specIncl L ≫ Spec.map (CommRingCat.ofHom (e' : K →+* L)) := by
  rw [specEmb, specIncl, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact (he x).symm

/-- The comparison `A ×_{K,e} ℚ̄ → A ×_{K,e'} L` (the base-change square along `Spec ℚ̄ → Spec L`). -/
noncomputable def cmpL (L : IntermediateField ℚ Qbar) (X : CategoryTheory.Over (Spec (CommRingCat.of K)))
    (e : K →ₐ[ℚ] Qbar) (e' : K →ₐ[ℚ] L) (he : ∀ x, (e' x : Qbar) = e x) :
    Limits.pullback X.hom (specEmb K e) ⟶
      Limits.pullback X.hom (Spec.map (CommRingCat.ofHom (e' : K →+* L))) :=
  Limits.pullback.lift (Limits.pullback.fst _ _) (Limits.pullback.snd _ _ ≫ specIncl L)
    (by rw [Limits.pullback.condition, specEmb_factor K L e e' he, Category.assoc])

/-- **Input: EGA IV₃ 8.8.2 (i), surjectivity part, for `ℚ̄ = colim L` (locator UNVERIFIED).**
Every morphism `A ×_{K,e₁} ℚ̄ → B ×_{K,e₂} ℚ̄` over `ℚ̄` between base changes of abelian
varieties over a number field `K ⊆ ℚ̄` comes from a morphism `ψ : A ×_{K,e₁'} L → B ×_{K,e₂'} L`
over a number field `L ⊆ ℚ̄` through which `e₁, e₂` factor (`φ` is the base change of `ψ`: it
is the map compatible with `ψ` under the cartesian squares `cmpL`). Hypotheses of 8.8.2: `A`
quasi-compact quasi-separated (proper), `B` locally of finite presentation (smooth). -/
def MorphismsDescend : Prop :=
  ∀ (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] (A B : AbVar K)
    (e₁ e₂ : K →ₐ[ℚ] Qbar)
    (φ : (CategoryTheory.Over.pullback (specEmb K e₁)).obj A.X ⟶
      (CategoryTheory.Over.pullback (specEmb K e₂)).obj B.X),
    ∃ (L : IntermediateField ℚ Qbar) (_ : FiniteDimensional ℚ L) (e₁' e₂' : K →ₐ[ℚ] L)
      (he₁ : ∀ x, (e₁' x : Qbar) = e₁ x) (he₂ : ∀ x, (e₂' x : Qbar) = e₂ x)
      (ψ : Limits.pullback A.X.hom (Spec.map (CommRingCat.ofHom (e₁' : K →+* L))) ⟶
        Limits.pullback B.X.hom (Spec.map (CommRingCat.ofHom (e₂' : K →+* L)))),
      φ.left ≫ cmpL K L B.X e₂ e₂' he₂ = cmpL K L A.X e₁ e₁' he₁ ≫ ψ

/-- `σ ∈ G_L` fixes `Spec ℚ̄ → Spec L`. -/
theorem specGal_specIncl (L : IntermediateField ℚ Qbar) (σ : Gal) (hσ : σ ∈ L.fixingSubgroup) :
    specGal σ ≫ specIncl L = specIncl L := by
  rw [specGal, specIncl, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact (IntermediateField.mem_fixingSubgroup_iff L σ).mp hσ x x.2

/-- **`HomDescends` from EGA IV₃ 8.8.2 (glue, proved): the descent bookkeeping.** A morphism
that is the base change of one over `L` is fixed by conjugation through `G_L`. -/
theorem homDescends_of_morphismsDescend (hM : MorphismsDescend) : HomDescends := by
  intro K _ A B e₁ e₂ φ
  obtain ⟨L, hL, e₁', e₂', he₁, he₂, ψ, hψ⟩ := hM K A B e₁ e₂ φ
  refine ⟨L.fixingSubgroup, IntermediateField.fixingSubgroup_isOpen L, fun σ hσ hf hg => ?_⟩
  symm
  apply G4Conj.conj_unique
  -- `cmp_σ ≫ cmpL = cmpL`
  have hcL : ∀ (X : CategoryTheory.Over (Spec (CommRingCat.of K))) (e : K →ₐ[ℚ] Qbar)
      (e' : K →ₐ[ℚ] L) (he : ∀ x, (e' x : Qbar) = e x)
      (h : specEmb K e = specGal σ ≫ specEmb K e),
      G4Conj.cmp X (specGal σ) h ≫ cmpL K L X e e' he = cmpL K L X e e' he := by
    intro X e e' he h
    apply Limits.pullback.hom_ext
    · simp [cmpL]
    · simp only [cmpL, Category.assoc, Limits.pullback.lift_snd]
      rw [G4Conj.cmp_snd_assoc, specGal_specIncl L σ hσ]
  apply Limits.pullback.hom_ext
  · have e1 : Limits.pullback.fst B.X.hom (specEmb K e₂) =
        cmpL K L B.X e₂ e₂' he₂ ≫ Limits.pullback.fst _ _ := by simp [cmpL]
    rw [Category.assoc, G4Conj.cmp_fst, Category.assoc, e1, reassoc_of% hψ,
      reassoc_of% (hcL A.X e₁ e₁' he₁ hf)]
  · rw [Category.assoc, G4Conj.cmp_snd, Category.assoc]
    have h1 : φ.left ≫ Limits.pullback.snd B.X.hom (specEmb K e₂) =
        Limits.pullback.snd A.X.hom (specEmb K e₁) := CategoryTheory.Over.w φ
    rw [reassoc_of% h1, h1, G4Conj.cmp_snd]

/-- `G_K` fixes every embedding of the Galois field `K`. -/
theorem embAct_symm_of_mem [IsGalois ℚ K] (σ : Gal) (hσ : σ ∈ K.fixingSubgroup)
    (e : K →ₐ[ℚ] Qbar) : (embAct K σ).symm e = e := by
  ext x
  have hx : e x ∈ K := by
    have hmem : e x ∈ e.fieldRange := ⟨x, rfl⟩
    rw [AlgHom.fieldRange_of_normal e] at hmem
    exact hmem
  have hσ' : σ⁻¹ ∈ K.fixingSubgroup := K.fixingSubgroup.inv_mem hσ
  exact (IntermediateField.mem_fixingSubgroup_iff K _).mp hσ' _ hx

/-- The stabilizer of a lattice element, as a subgroup. -/
def stabSub (A : AbVar K) (m : HomLattice (conjData K A).A) : Subgroup Gal where
  carrier := {σ | conjAction K A σ m = m}
  one_mem' := by simp
  mul_mem' {σ τ} hσ hτ := by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_mul, LinearEquiv.mul_apply, hτ, hσ]
  inv_mem' {σ} hσ := by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← hσ]
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl

/-- **Continuity of the conjugation action (glue, proved from `HomDescends`).** -/
theorem conjAction_continuous (hD : HomDescends) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (A : AbVar K) (m : HomLattice (conjData K A).A) :
    IsOpen {σ : Gal | conjAction K A σ m = m} := by
  classical
  choose U hUo hU using fun ij : (K →ₐ[ℚ] Qbar) × (K →ₐ[ℚ] Qbar) =>
    hD K A A ij.1 ij.2 (m ij).hom
  let W : Set Gal := (K.fixingSubgroup : Set Gal) ∩ ⋂ ij, (U ij : Set Gal)
  have hWo : IsOpen W :=
    (IntermediateField.fixingSubgroup_isOpen K).inter (isOpen_iInter_of_finite fun ij => hUo ij)
  have hW1 : (1 : Gal) ∈ W :=
    ⟨K.fixingSubgroup.one_mem, Set.mem_iInter.mpr fun ij => (U ij).one_mem⟩
  have hWS : W ⊆ (stabSub K A m : Set Gal) := by
    rintro σ ⟨hσK, hσU⟩
    rw [Set.mem_iInter] at hσU
    show conjAction K A σ m = m
    rw [conjAction_apply]
    funext ij
    obtain ⟨i, j⟩ := ij
    apply AbVar.Hom.ext'
    rw [conjAct_apply, conjHom_hom]
    have aux : ∀ (i' j' : K →ₐ[ℚ] Qbar) (hi : i' = i) (hj : j' = j)
        (hf : specEmb K i = specGal σ ≫ specEmb K i')
        (hg : specEmb K j = specGal σ ≫ specEmb K j'),
        G4Conj.conj A.X A.X (specGal σ) hf hg (m (i', j')).hom = (m (i, j)).hom := by
      intro i' j' hi hj hf hg
      subst hi hj
      exact hU (i', j') σ (hσU (i', j')) hf hg
    exact aux _ _ (embAct_symm_of_mem K σ hσK i) (embAct_symm_of_mem K σ hσK j) _ _
  have hS : IsOpen (stabSub K A m : Set Gal) :=
    Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hWo.mem_nhds hW1) hWS)
  exact hS

/-- **G4 for a model `A/K`, continuity discharged.** As `homField_of_model`, with `hcont`
replaced by the input `HomDescends`. -/
theorem homField_of_model' (hHFF : HomFreeFinite) (hD : HomDescends) [FiniteDimensional ℚ K]
    [IsGalois ℚ K] (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0) (A : AbVar K)
    (hdim : ∀ e, ((conjData K A).A e).dim = 2)
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hinert : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, conjAction K A s = 1) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, conjAction K A σ = 1) ∧
      Module.finrank ℚ L ≤ ZInQ.heightD ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) :=
  homField_of_model K hHFF hKF A hdim (conjAction_continuous K hD A) T hK hinert



/-- **G4 for a model `A/K`, final form.** Leaves: `PkgI3.HomFreeFinite` (Mumford §19 Thm 3) and
`MorphismsDescend` (EGA IV₃ 8.8.2). Remaining hypotheses: `hdim` (dimension of base change),
`hK` (G2's output) and `hinert` (inertia outside `T` trivial on the lattice: NOS + the action on
Tate modules, see `inertia_of_tate`). -/
theorem homField_of_model_final (hHFF : HomFreeFinite) (hM : MorphismsDescend)
    [FiniteDimensional ℚ K] [IsGalois ℚ K] (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0)
    (A : AbVar K) (hdim : ∀ e, ((conjData K A).A e).dim = 2)
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hinert : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, conjAction K A s = 1) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, conjAction K A σ = 1) ∧
      Module.finrank ℚ L ≤ ZInQ.heightD ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) :=
  homField_of_model' K hHFF (homDescends_of_morphismsDescend hM) hKF A hdim T hK hinert

/-! ### Inertia from good reduction

`InertiaFixesHoms` is the input: at a place `w` of `ℚ̄` where both varieties have good reduction,
inertia fixes every homomorphism between their base changes. It is a consequence of
Néron–Ogg–Shafarevich (Serre–Tate 1968, Thm 1: inertia acts trivially on `T_ℓ` for `ℓ ≠ p`; the
leaf `PkgI2.NeronOggShafarevich`) and the faithfulness of the `ℓ`-adic realization (Mumford §19
Thm 3; `tateHom_injective` above), through the equivariance of the realization under
conjugation. That equivariance is glue that is not formalized here. Stated over the genuine
objects (`PkgI2.HasGoodReduction`, `inertiaGQ`, `G4Conj.conj`). -/

/-- **Input (Serre–Tate 1968 Thm 1 + Mumford §19 Thm 3 + equivariance; derivation not
formalized).** -/
def InertiaFixesHoms : Prop :=
  ∀ (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] (A B : AbVar K)
    (e₁ e₂ : K →ₐ[ℚ] Qbar)
    (φ : (CategoryTheory.Over.pullback (specEmb K e₁)).obj A.X ⟶
      (CategoryTheory.Over.pullback (specEmb K e₂)).obj B.X)
    (w : ValuationSubring Qbar),
    PkgI2.HasGoodReduction (ObjBridge.toGrp A) (w.comap (e₁ : K →+* Qbar)) →
    PkgI2.HasGoodReduction (ObjBridge.toGrp B) (w.comap (e₂ : K →+* Qbar)) →
    ∀ s ∈ inertiaGQ w, ∀ (hf : specEmb K e₁ = specGal s ≫ specEmb K e₁)
      (hg : specEmb K e₂ = specGal s ≫ specEmb K e₂),
      G4Conj.conj A.X B.X (specGal s) hf hg φ = φ

/-- **The inertia hypothesis of G4 (glue, proved from `InertiaFixesHoms`).** If `K` is unramified
outside `T` and `A` has good reduction at every place of `K` above every `p ∉ T` (G3's output),
inertia above `p ∉ T` acts trivially on the Hom lattice of the conjugates. -/
theorem conjAction_inertia (hI : InertiaFixesHoms) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (A : AbVar K) (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hgood : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ e : K →ₐ[ℚ] Qbar, PkgI2.HasGoodReduction (ObjBridge.toGrp A) (w.comap (e : K →+* Qbar))) :
    ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, conjAction K A s = 1 := by
  intro p hp hpT w hw
  intro (σ : Gal) (hσ : σ ∈ inertiaGQ w)
  have hσK : σ ∈ K.fixingSubgroup := hK p hp hpT w hw hσ
  apply LinearEquiv.ext
  intro m
  show conjAct K A σ m = m
  funext ij
  obtain ⟨i, j⟩ := ij
  apply AbVar.Hom.ext'
  rw [conjAct_apply, conjHom_hom]
  have aux : ∀ (i' j' : K →ₐ[ℚ] Qbar) (hi : i' = i) (hj : j' = j)
      (hf : specEmb K i = specGal σ ≫ specEmb K i')
      (hg : specEmb K j = specGal σ ≫ specEmb K j'),
      G4Conj.conj A.X A.X (specGal σ) hf hg (m (i', j')).hom = (m (i, j)).hom := by
    intro i' j' hi hj hf hg
    subst hi hj
    exact hI K A A i' j' (m (i', j')).hom w (hgood p hp hpT w hw i') (hgood p hp hpT w hw j')
      σ hσ hf hg
  exact aux _ _ (embAct_symm_of_mem K σ hσK i) (embAct_symm_of_mem K σ hσK j) _ _

/-- **G4 for a model `A/K`, all analytic inputs as leaves.** Leaves/inputs: `HomFreeFinite`
(Mumford §19 Thm 3), `MorphismsDescend` (EGA IV₃ 8.8.2), `InertiaFixesHoms` (Serre–Tate +
Mumford + equivariance). Hypotheses from other glue steps: `hK` (G2), `hgood` (G3), `hdim`
(dimension of base change, missing from Mathlib). -/
theorem homField_of_model_leaves (hHFF : HomFreeFinite) (hM : MorphismsDescend)
    (hI : InertiaFixesHoms) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0)
    (A : AbVar K) (hdim : ∀ e, ((conjData K A).A e).dim = 2)
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hgood : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ e : K →ₐ[ℚ] Qbar, PkgI2.HasGoodReduction (ObjBridge.toGrp A) (w.comap (e : K →+* Qbar))) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, conjAction K A σ = 1) ∧
      Module.finrank ℚ L ≤ ZInQ.heightD ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) :=
  homField_of_model_final K hHFF hM hKF A hdim T hK (conjAction_inertia K hI A T hK hgood)

end Lattice

/-! ## What G7 receives: the Hom field feeds `GlueDescent.B3Q.b3_degree_le_QM`

`b3_degree_le_QM` needs a finite Galois `L` with `[L:ℚ] ≤ D`, unramified outside `T = ramSet S u`
(ideal-theoretic form), and the cocycle `ε` of the scalar descent data inflated from `Gal(L/ℚ)`.
The first three are G4's output above; the last is G7's own instantiation (the descent data
`μ_σ` are elements of the lattice, so a field defining the lattice defines `ε`), kept here as the
hypothesis `hdesc`. -/

section Feed

/-- **G4 → G7.** The Hom field of `homField_le_heightD`, with `T = ramSet S u`, is a valid input
of `GlueDescent.B3Q.b3_degree_le_QM`: the scalar-descent output (`χ`, `β`, `L' ⊇ L` Galois with
`[L':ℚ] ≤ Q_R·M_S(u)`) follows. -/
theorem b3_of_homField (hHasse : GlueDescent.B2Q.LeafHasse)
    (hTwo : GlueDescent.B2Q.LeafLocalTwo) (hSq : GlueDescent.B2Q.LeafSqrtCrit)
    (hUnr : GlueDescent.B2Q.LeafUnramified) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (R : ℝ)
    (hRD : (ZInQ.heightD : ℝ) ≤ R) (hRS : ∀ p ∈ S, (p : ℝ) ≤ R) (hR12 : (10 : ℝ) ^ 12 ≤ R)
    (u : ℚ) {M : Type*} [AddCommGroup M]
    (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0)
    {r : ℕ} (hr : r ≤ 16 * ZInQ.heightF0 ^ 2) (b : Module.Basis (Fin r) ℤ M)
    (ρ : Gal →* (M ≃ₗ[ℤ] M))
    (hcont : ∀ m : M, IsOpen {σ : Gal | ρ σ m = m})
    (hK : GalUnramifiedOutside K (GlueDescent.ramSet S u))
    (hinert : ∀ p : ℕ, p.Prime → p ∉ GlueDescent.ramSet S u → ∀ w : ValuationSubring Qbar,
      LiesOver w p → ∀ s ∈ inertiaGQ w, ρ s = 1)
    (hdesc : ∀ L : IntermediateField ℚ Qbar, (∀ σ ∈ L.fixingSubgroup, ρ σ = 1) →
      ∃ ε : GlueDescent.B2Q.GQ → GlueDescent.B2Q.GQ → ℂˣ, GlueDescent.B2.IsSignCocycle ε ∧
        GlueDescent.B2Q.InflatedFrom L ε ∧ ε 1 1 = 1)
    (η : GlueDescent.B2Q.GQ →* ℂˣ) (hη : ∀ x, η x ^ 2 = 1) (hηl : IsLocallyConstant η) :
    ∃ (L : IntermediateField ℚ Qbar) (ε : GlueDescent.B2Q.GQ → GlueDescent.B2Q.GQ → ℂˣ)
      (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N) (β : GlueDescent.B2Q.GQ → ℂˣ)
      (L' : IntermediateField ℚ Qbar),
      Module.finrank ℚ L ≤ ZInQ.heightD ∧ K ≤ L ∧
      IsLocallyConstant β ∧ (∀ x, β x ^ 2 = GlueDescent.B2Q.galChar χ x) ∧
      (∀ x y, β x * β y = ε x y * β (x * y)) ∧
      L ≤ L' ∧ FiniteDimensional ℚ L' ∧ IsGalois ℚ L' ∧
      (Module.finrank ℚ L' : ℝ) ≤ ZInQ.heightQ R * ZInQ.contactSupport S u := by
  obtain ⟨L, hfd, hgal, hKL, hdef, hdeg, -, hram⟩ :=
    homField_le_heightD K hKF hr b ρ hcont (GlueDescent.ramSet S u) hK hinert
  obtain ⟨ε, hε, hinf, h11⟩ := hdesc L hdef
  obtain ⟨N, hN, χ, β, L', hβl, hβs, hβe, hle, hfd', hgal', -, hdeg'⟩ :=
    GlueDescent.B3Q.b3_degree_le_QM hHasse hTwo hSq hUnr S hS R hRD hRS hR12 u L hdeg ε hε hinf
      h11 hram η hη hηl
  exact ⟨L, ε, N, hN, χ, β, L', hdeg, hKL, hβl, hβs, hβe, hle, hfd', hgal', hdeg'⟩

/-- **G4 → the CM branch.** `GlueAssembly.CMOutput` takes `d = [L:ℚ]` with `1 ≤ d ≤ D` (reals);
the Hom field supplies it. -/
theorem cm_degree_of_homField (L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ L]
    (hL : Module.finrank ℚ L ≤ ZInQ.heightD) :
    (1 : ℝ) ≤ (Module.finrank ℚ L : ℝ) ∧ (Module.finrank ℚ L : ℝ) ≤ (ZInQ.heightD : ℝ) :=
  ⟨by exact_mod_cast Module.finrank_pos, by exact_mod_cast hL⟩


end Feed

end G4WeilRes

#print axioms G4WeilRes.unramifiedAt_of_inertia_le
#print axioms G4WeilRes.galUnramifiedOutside_iff
#print axioms G4WeilRes.homField_core
#print axioms G4WeilRes.homField_le_heightD
#print axioms G4WeilRes.homField_of_conjugates
#print axioms G4WeilRes.b3_of_homField
#print axioms G4WeilRes.isConjAction_unique
#print axioms G4WeilRes.conjData
#print axioms G4WeilRes.conjActionExists
#print axioms G4Conj.conj_isMonHom
#print axioms G4WeilRes.homField_of_model
#print axioms G4WeilRes.homField_of_model'
#print axioms G4WeilRes.conjAction_continuous
#print axioms G4WeilRes.homDescends_of_morphismsDescend
#print axioms G4WeilRes.homField_of_model_final
#print axioms G4WeilRes.conjAction_inertia
#print axioms G4WeilRes.homField_of_model_leaves
#print axioms G4WeilRes.tateHom_injective
#print axioms G4WeilRes.inertia_of_tate
