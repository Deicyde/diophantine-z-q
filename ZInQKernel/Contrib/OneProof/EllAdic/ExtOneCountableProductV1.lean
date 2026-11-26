import ZInQKernel.Contrib.OneProof.EllAdic.CountableProductShortExactV1
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

set_option autoImplicit false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace RC53.EllAdic

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

private noncomputable def extOneBoundary (T : C) {S : ShortComplex C} (h : S.ShortExact)
    (f : T ⟶ S.X₃) : Ext.{w} T S.X₁ 1 :=
  (Ext.mk₀ f).comp h.extClass (zero_add 1)

private lemma extOneBoundary_natural (T : C) {S R : ShortComplex C}
    (hS : S.ShortExact) (hR : R.ShortExact) (pr : S ⟶ R) (f : T ⟶ S.X₃) :
    (extOneBoundary T hS f).comp (Ext.mk₀ pr.τ₁) (add_zero 1) =
      extOneBoundary T hR (f ≫ pr.τ₃) := by
  unfold extOneBoundary
  rw [Ext.comp_assoc_of_third_deg_zero, hS.extClass_naturality hR pr,
    ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]

private lemma extOneBoundary_surj (T : C) {S : ShortComplex C} (h : S.ShortExact)
    [Injective S.X₂] : Function.Surjective (extOneBoundary T h : (T ⟶ S.X₃) → Ext.{w} T S.X₁ 1) := by
  intro x
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ T h x
    (Ext.eq_zero_of_injective (n := 0) _) (zero_add 1)
  exact ⟨Ext.addEquiv₀ z, by simpa only [extOneBoundary, Ext.mk₀_addEquiv₀_apply] using hz⟩

private lemma extOneBoundary_zero_iff (T : C) {S : ShortComplex C} (h : S.ShortExact)
    (f : T ⟶ S.X₃) : (extOneBoundary T h f : Ext.{w} T S.X₁ 1) = 0 ↔
      ∃ g : T ⟶ S.X₂, g ≫ S.g = f := by
  constructor
  · intro hz
    obtain ⟨z, hz'⟩ := Ext.covariant_sequence_exact₃ T h (Ext.mk₀ f) (zero_add 1) hz
    refine ⟨Ext.addEquiv₀ z, ?_⟩
    apply (Ext.addEquiv₀ (X := T) (Y := S.X₃)).symm.injective
    change Ext.mk₀ (Ext.addEquiv₀ z ≫ S.g) = Ext.mk₀ f
    rwa [← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]
  · rintro ⟨g, rfl⟩
    unfold extOneBoundary
    rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero, h.comp_extClass, Ext.comp_zero]

variable [HasLimitsOfShape (Discrete ℕ) C]

/-- The canonical product comparison on first Ext, with the actual product
projections as its coordinates, before proving that it is an equivalence. -/
noncomputable def extOnePiComparison (T : C) (F : ℕ → C) :
    Ext.{w} T (∏ᶜ F) 1 →+ (∀ n, Ext.{w} T (F n) 1) where
  toFun x n := x.comp (Ext.mk₀ (Pi.π F n)) (add_zero 1)
  map_zero' := by
    funext n
    exact map_zero ((Ext.mk₀ (Pi.π F n)).postcomp T (add_zero 1))
  map_add' x y := by
    funext n
    exact map_add ((Ext.mk₀ (Pi.π F n)).postcomp T (add_zero 1)) x y

/-- First Ext commutes with countable products when countable products are
exact. Both directions use the same connecting maps via their projections. -/
theorem extOnePiComparison_bijective [EnoughInjectives C]
    [HasExactLimitsOfShape (Discrete ℕ) C] (T : C) (F : ℕ → C) :
    Function.Bijective (extOnePiComparison T F : Ext.{w} T (∏ᶜ F) 1 →+ (∀ n, Ext.{w} T (F n) 1)) := by
  classical
  let I (n : ℕ) : InjectivePresentation (F n) :=
    (EnoughInjectives.presentation (F n)).some
  let f (n : ℕ) := (I n).f
  let J (n : ℕ) := (I n).J
  let Q (n : ℕ) := cokernel (f n)
  let S (n : ℕ) := ShortComplex.mk (f n) (cokernel.π (f n)) (cokernel.condition (f n))
  have hS (n : ℕ) : (S n).ShortExact := by
    refine ShortComplex.ShortExact.mk' ((S n).exact_of_g_is_cokernel ?_) (I n).mono inferInstance
    exact cokernelIsCokernel (f n)
  let P := countableProductShortComplex S
  have hP : P.ShortExact := countableProductShortComplex_shortExact S hS
  let : ∀ n, Injective (J n) := fun n => (I n).injective
  let : Injective P.X₂ := by
    change Injective (∏ᶜ J)
    infer_instance
  have hcoord (u : T ⟶ P.X₃) (n : ℕ) :
      extOnePiComparison T F (extOneBoundary T hP u : Ext.{w} T (∏ᶜ F) 1) n =
        extOneBoundary T (hS n) (u ≫ Pi.π Q n) :=
    extOneBoundary_natural T hP (hS n) (countableProductShortComplexProjection S n) u
  have hzero (x : Ext.{w} T (∏ᶜ F) 1) (hx : extOnePiComparison T F x = 0) : x = 0 := by
    obtain ⟨u, hu⟩ := extOneBoundary_surj T hP x
    have hz (n : ℕ) : (extOneBoundary T (hS n) (u ≫ Pi.π Q n) : Ext.{w} T (F n) 1) = 0 := by
      have hn := hcoord u n
      rw [hu] at hn
      exact hn.symm.trans (congrFun hx n)
    choose g hg using fun n => (extOneBoundary_zero_iff T (hS n) _).1 (hz n)
    have hgP : Pi.lift g ≫ P.g = u := by
      apply Pi.hom_ext
      intro n
      change (Pi.lift g ≫ Limits.Pi.map (fun k => (S k).g)) ≫ Pi.π Q n = u ≫ Pi.π Q n
      rw [Category.assoc, Pi.map_π, ← Category.assoc, Pi.lift_comp_π]
      exact hg n
    exact hu.symm.trans ((extOneBoundary_zero_iff T hP u).2 ⟨Pi.lift g, hgP⟩)
  constructor
  · intro x y hxy
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hxy, sub_self]
  · intro x
    choose u hu using fun n => extOneBoundary_surj T (hS n) (x n)
    let uP : T ⟶ P.X₃ := (Pi.lift u : T ⟶ ∏ᶜ Q)
    refine ⟨extOneBoundary T hP uP, ?_⟩
    funext n
    have hπ : uP ≫ Pi.π Q n = u n := Pi.lift_comp_π u n
    exact (hcoord uP n).trans ((congrArg (extOneBoundary T (hS n)) hπ).trans (hu n))

end RC53.EllAdic
