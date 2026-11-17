/-
H5 lane3 Step 1, R3 sub-gap `TrivialOfSectionsBothWays` (PicZeroSections.lean), reduced to ONE
primitive. 2026-11-17. New file. SOURCE-ONLY, UNCOMPILED. Universe u, any field.

PROVED here, modulo compile: `trivialOfSectionsBothWays (hT : TensorHomNeZero)`.
1. A nonzero `H⁰` gives a nonzero morphism `θ : 𝟙_ ⟶ L`, via W07 `H.zeroLinearEquiv` and
   `unitHomAddEquiv`.
2. `c := λ⁻¹ ≫ (θ ⊗ φ) ≫ e : 𝟙_ ⟶ 𝟙_` is nonzero. It is the multiplication `smulHom a` by
   `a := c(1) ∈ Γ(X, O_X)`. That `a` is a unit (PMGF `nonzero_globalFunctions_are_units`), so `c`
   is an isomorphism.
3. Hence `θ ⊗ φ` is an isomorphism. `tensorHom_def` makes `θ ▷ 𝟙` split mono, so `θ` is mono.
   `tensorHom_def'` makes `θ ▷ M` split epi; whiskering by `Mᵛ` with `M ⊗ Mᵛ ≅ 𝟙` makes `θ ▷ 𝟙`
   split epi, so `θ` is split epi. A mono split epi is an iso, so `L ≅ 𝟙_`.

The only remaining primitive is `TensorHomNeZero` (UNPROVED, true): on an integral scheme, the
tensor product of two nonzero morphisms `𝟙_ ⟶ L` and `𝟙_ ⟶ M` into invertible sheaves is nonzero.
Plan, with W07 support named:
* choose an affine `U` trivializing both `L` and `M` (W07 `exists_isFreeGenerator₂`);
* restriction to `U` is injective (integral scheme; Mathlib `germ_injective_of_isIntegral`);
* compute on `U` with free generators (W07 `IsFreeGenerator.tmulSection`) in the domain `Γ(U, O)`.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.PicZeroSections
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.GlobalSection

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2NOS.Step1

/-- The remaining primitive (UNPROVED, true): nonvanishing of tensor products on integral
schemes. -/
def TensorHomNeZero : Prop :=
  ∀ {X : Scheme.{u}} [IsIntegral X] (L M : X.Modules) [L.IsInvertible] [M.IsInvertible]
    (θ : 𝟙_ X.Modules ⟶ L) (φ : 𝟙_ X.Modules ⟶ M), θ ≠ 0 → φ ≠ 0 → θ ⊗ₘ φ ≠ 0

theorem exists_hom_ne_zero {X : Scheme.{u}} (L : X.Modules) (h : ¬ Subsingleton (L.H 0)) :
    ∃ θ : 𝟙_ X.Modules ⟶ L, θ ≠ 0 := by
  haveI : Nontrivial (L.H 0) := not_subsingleton_iff_nontrivial.mp h
  obtain ⟨v, hv⟩ := exists_ne (0 : L.H 0)
  refine ⟨(Scheme.Modules.unitHomAddEquiv L).symm (Scheme.Modules.H.zeroLinearEquiv L v), ?_⟩
  intro h0
  apply hv
  have h1 : Scheme.Modules.H.zeroLinearEquiv L v = 0 := by
    have := congrArg (Scheme.Modules.unitHomAddEquiv L) h0
    rwa [AddEquiv.apply_symm_apply, map_zero] at this
  exact (Scheme.Modules.H.zeroLinearEquiv L).map_eq_zero_iff.mp h1

/-- A nonzero endomorphism of the structure sheaf of a proper integral `K`-scheme is an
isomorphism. -/
theorem isIso_of_ne_zero_endo_unit {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] [IsIntegral X]
    (c : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) (hc : c ≠ 0) : IsIso c := by
  set a : Γ(X, ⊤) := Scheme.Modules.unitHomAddEquiv (Scheme.Modules.unit X) c with ha
  have hca : c = (Scheme.Modules.unit X).smulHom a := by
    apply (Scheme.Modules.unitHomAddEquiv (Scheme.Modules.unit X)).injective
    rw [Scheme.Modules.unitHomAddEquiv_apply, Scheme.Modules.unitHomAddEquiv_apply,
      Scheme.Modules.smulHom_app_top_apply]
    exact (mul_one a).symm
  have ha0 : a ≠ 0 := by
    intro h0
    apply hc
    rw [hca, h0, Scheme.Modules.smulHom_zero]
  obtain ⟨w, hw⟩ :=
    ZInQ.Contrib.CloudR2NOS.FieldAmpleness.PureMathlibGlobalFunctions.nonzero_globalFunctions_are_units
      f a ha0
  rw [hca]
  refine ⟨⟨(Scheme.Modules.unit X).smulHom ↑w⁻¹, ?_, ?_⟩⟩
  · rw [← Scheme.Modules.smulHom_mul, ← hw, Units.inv_mul, Scheme.Modules.smulHom_one]
  · rw [← Scheme.Modules.smulHom_mul, ← hw, Units.mul_inv, Scheme.Modules.smulHom_one]

/-- If `θ ⊗ φ` is an isomorphism (with `M` invertible), then `θ` is an isomorphism. -/
theorem isIso_of_isIso_tensorHom {X : Scheme.{u}} {L M : X.Modules} [M.IsInvertible]
    (θ : 𝟙_ X.Modules ⟶ L) (φ : 𝟙_ X.Modules ⟶ M) [IsIso (θ ⊗ₘ φ)] : IsIso θ := by
  have h1 : θ ⊗ₘ φ = θ ▷ 𝟙_ X.Modules ≫ L ◁ φ := MonoidalCategory.tensorHom_def θ φ
  have h2 : θ ⊗ₘ φ = 𝟙_ X.Modules ◁ φ ≫ θ ▷ M := tensorHom_def' θ φ
  haveI : IsSplitMono (θ ▷ 𝟙_ X.Modules) :=
    IsSplitMono.mk' ⟨L ◁ φ ≫ inv (θ ⊗ₘ φ), by rw [← Category.assoc, ← h1, IsIso.hom_inv_id]⟩
  haveI : IsSplitEpi (θ ▷ M) :=
    IsSplitEpi.mk' ⟨inv (θ ⊗ₘ φ) ≫ 𝟙_ X.Modules ◁ φ, by
      rw [Category.assoc, ← h2, IsIso.inv_hom_id]⟩
  have hρ : θ = (ρ_ (𝟙_ X.Modules)).inv ≫ θ ▷ 𝟙_ X.Modules ≫ (ρ_ L).hom := by
    rw [MonoidalCategory.whiskerRight_id]
    simp
  haveI : Mono θ := by
    rw [hρ]
    infer_instance
  haveI : IsSplitEpi ((θ ▷ M) ▷ Scheme.Modules.dual M) :=
    (inferInstance : IsSplitEpi ((tensorRight (Scheme.Modules.dual M)).map (θ ▷ M)))
  haveI : IsSplitEpi (θ ▷ (M ⊗ Scheme.Modules.dual M)) := by
    rw [whiskerRight_tensor]
    infer_instance
  have hE : θ ▷ 𝟙_ X.Modules =
      𝟙_ X.Modules ◁ (Scheme.Modules.tensorObjDualIsoUnit M).inv ≫
        θ ▷ (M ⊗ Scheme.Modules.dual M) ≫ L ◁ (Scheme.Modules.tensorObjDualIsoUnit M).hom := by
    rw [← whisker_exchange, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
      Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id, Category.id_comp]
  haveI : IsSplitEpi (θ ▷ 𝟙_ X.Modules) := by
    rw [hE]
    infer_instance
  haveI : IsSplitEpi θ := by
    rw [hρ]
    infer_instance
  exact isIso_of_mono_of_isSplitEpi θ

/-- `TrivialOfSectionsBothWays`, PROVED from `TensorHomNeZero`. -/
theorem trivialOfSectionsBothWays (hT : TensorHomNeZero.{u}) :
    TrivialOfSectionsBothWays.{u} := by
  intro K _ X f _ _ ε hε L M _ _ he hL hM
  obtain ⟨e⟩ := he
  obtain ⟨θ, hθ⟩ := exists_hom_ne_zero L hL
  obtain ⟨φ, hφ⟩ := exists_hom_ne_zero M hM
  have hdecomp : θ ⊗ₘ φ =
      (λ_ (𝟙_ X.Modules)).hom ≫ ((λ_ (𝟙_ X.Modules)).inv ≫ (θ ⊗ₘ φ) ≫ e.hom) ≫ e.inv := by
    simp
  have hc : (λ_ (𝟙_ X.Modules)).inv ≫ (θ ⊗ₘ φ) ≫ e.hom ≠ 0 := by
    intro h0
    apply hT L M θ φ hθ hφ
    rw [hdecomp, h0, Limits.zero_comp, Limits.comp_zero]
  haveI := isIso_of_ne_zero_endo_unit f _ hc
  haveI : IsIso (θ ⊗ₘ φ) := by
    rw [hdecomp]
    infer_instance
  haveI := isIso_of_isIso_tensorHom θ φ
  exact ⟨(asIso θ).symm⟩

end ZInQ.Contrib.CloudR2NOS.Step1
