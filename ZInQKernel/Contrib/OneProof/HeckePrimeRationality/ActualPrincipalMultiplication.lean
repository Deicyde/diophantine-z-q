import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic

/-!
# The actual principal-group multiplication map

These are the genuine analytic modular-form spaces and pointwise products.
The range description records exactly the still-unproved spanning obligation;
it does not identify the product span with the whole space. Geometric
section-space multiplication must be bound to these objects separately.
-/

noncomputable section
set_option autoImplicit false
open Matrix.SpecialLinearGroup UpperHalfPlane Filter
open scoped TensorProduct MatrixGroups Topology

namespace ZInQ.Contrib.HeckePrimeRationality.PrincipalMultiplication

/-- The mapped integral principal congruence group. -/
abbrev principalGroup (N : ℕ) := (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

/-- Genuine weight-j forms, not a coordinate or divisor-space replacement. -/
abbrev Form (N j : ℕ) := ModularForm (principalGroup N) (j : ℤ)

/-- Pointwise multiplication with only the necessary natural-to-integer weight transport. -/
def product (N j j' : ℕ) (f : Form N j) (g : Form N j') : Form N (j + j') :=
  (f.mul g).mcast (by omega)

@[simp] theorem product_apply (N j j' : ℕ) (f : Form N j) (g : Form N j') (τ : ℍ) :
    product N j j' f g τ = f τ * g τ := rfl

/-- The genuine complex-bilinear product. -/
def productLinear (N j j' : ℕ) : Form N j →ₗ[ℂ] Form N j' →ₗ[ℂ] Form N (j + j') where
  toFun f :=
    { toFun := product N j j' f
      map_add' := by
        intro g h
        ext τ
        change f τ * (g τ + h τ) = f τ * g τ + f τ * h τ
        exact mul_add _ _ _
      map_smul' := by
        intro c g
        ext τ
        change f τ * (c * g τ) = c * (f τ * g τ)
        ring }
  map_add' := by
    intro f g
    ext h τ
    change (f τ + g τ) * h τ = f τ * h τ + g τ * h τ
    exact add_mul _ _ _
  map_smul' := by
    intro c f
    ext g τ
    change (c * f τ) * g τ = c * (f τ * g τ)
    ring

/-- The actual tensor multiplication map, with the full actual modular-form target. -/
def multiplication (N j j' : ℕ) :
    Form N j ⊗[ℂ] Form N j' →ₗ[ℂ] Form N (j + j') :=
  TensorProduct.lift (productLinear N j j')

@[simp] theorem multiplication_tmul (N j j' : ℕ) (f : Form N j) (g : Form N j') :
    multiplication N j j' (f ⊗ₜ[ℂ] g) = product N j j' f g := rfl

@[simp] theorem multiplication_tmul_apply (N j j' : ℕ)
    (f : Form N j) (g : Form N j') (τ : ℍ) :
    multiplication N j j' (f ⊗ₜ[ℂ] g) τ = f τ * g τ := rfl

/-- The exact product range span; no assertion that it equals the whole space is made. -/
def productSpan (N j j' : ℕ) : Submodule ℂ (Form N (j + j')) :=
  Submodule.span ℂ {h | ∃ f g, product N j j' f g = h}

/-- Every tensor image is a sum of actual products, and conversely each actual product is an image. -/
theorem range_multiplication (N j j' : ℕ) :
    LinearMap.range (multiplication N j j') = productSpan N j j' := by
  apply le_antisymm
  · rintro _ ⟨z,rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul f g => exact Submodule.subset_span ⟨f,g,rfl⟩
    | add z w hz hw => rw [map_add]; exact Submodule.add_mem _ hz hw
  · rw [productSpan, Submodule.span_le]
    rintro h ⟨f,g,rfl⟩
    exact ⟨f ⊗ₜ[ℂ] g,rfl⟩

/-- This equivalence exposes the actual missing producer rather than assuming it. -/
theorem multiplication_surjective_iff (N j j' : ℕ) :
    Function.Surjective (multiplication N j j') ↔ productSpan N j j' = ⊤ := by
  rw [← LinearMap.range_eq_top, range_multiplication]

/-- Commuting the two real factors only transports the actual total weight. -/
theorem product_comm (N j j' : ℕ) (f : Form N j) (g : Form N j') :
    (product N j j' f g).mcast (by omega) = product N j' j g f := by
  ext τ
  exact mul_comm _ _

/-- There are no zero divisors among actual analytic forms, by the identity principle on ℍ. -/
theorem product_eq_zero_iff (N j j' : ℕ) (f : Form N j) (g : Form N j') :
    product N j j' f g = 0 ↔ f = 0 ∨ g = 0 := by
  constructor
  · intro hfg
    by_cases hf : f = 0
    · exact Or.inl hf
    right
    obtain ⟨τ,hτ⟩ : ∃ τ : ℍ, f τ ≠ 0 := by
      by_contra h
      apply hf
      ext τ
      simpa using (not_exists.mp h) τ
    have hne : ∀ᶠ w in 𝓝 τ, f w ≠ 0 :=
      (f.holo'.continuous.continuousAt).eventually_ne hτ
    have hz : ∀ᶠ w in 𝓝 τ, g w = 0 := by
      filter_upwards [hne] with w hw
      have he := congrArg (fun h : Form N (j + j') => h w) hfg
      change f w * g w = 0 at he
      exact (mul_eq_zero.mp he).resolve_left hw
    have hg : (g : ℍ → ℂ) = 0 :=
      UpperHalfPlane.eq_zero_of_frequently g.holo' (hz.filter_mono nhdsWithin_le_nhds).frequently
    ext w
    exact congrFun hg w
  · rintro (rfl | rfl) <;> ext τ <;> simp [product]

/-- Multiplication by a nonzero actual modular form is injective; no dimension premise is needed. -/
theorem product_left_injective (N j j' : ℕ) (f : Form N j) (hf : f ≠ 0) :
    Function.Injective (product N j j' f) := by
  intro g h he
  have hz : product N j j' f (g - h) = 0 := by
    ext τ
    have hτ := congrArg (fun u : Form N (j + j') => u τ) he
    change f τ * (g τ - h τ) = 0
    change f τ * g τ = f τ * h τ at hτ
    linear_combination hτ
  exact sub_eq_zero.mp ((product_eq_zero_iff N j j' f (g - h)).mp hz |>.resolve_left hf)

end ZInQ.Contrib.HeckePrimeRationality.PrincipalMultiplication
