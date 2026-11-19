import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Evaluation of Kähler differentials at a rational point

Let `O` be a local algebra over a field `k` together with a ring retraction `ρ : O → k` of the
constants, that is, a `k`-rational point. Then `a ↦ (a - ρ(a)) mod 𝔪²` is a `k`-derivation of
`O` with values in the cotangent space `𝔪/𝔪²` (`pointDerivation`), and its Kähler lift
`Ω[O/k] → 𝔪/𝔪²` (`pointEval`) is the evaluation of differentials at the point:
`D a ↦ (a - a(P)) mod 𝔪²`. For a unit `u` with value `1` and `a ∈ 𝔪`, the differential
`u⁻¹ • D a` evaluates to the class of `a` (`pointEval_unit_inv_smul_D`).

Locator: Hartshorne, *Algebraic Geometry*, II.8.7 (the conormal sequence of a rational point);
Matsumura, *Commutative Ring Theory*, Theorem 25.2.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.HodgeLineBinding

open KaehlerDifferential IsLocalRing

variable {k O : Type*} [Field k] [CommRing O] [IsLocalRing O] [Algebra k O]

/-- THEOREM (proved). A retraction of the constants vanishes on the maximal ideal: its kernel is
a maximal ideal, hence the maximal ideal. Locator: Mathlib, `IsLocalRing.mem_maximalIdeal`. -/
theorem retraction_eq_zero_of_mem (ρ : O →+* k) (hρ : ∀ c : k, ρ (algebraMap k O c) = c)
    {m : O} (hm : m ∈ maximalIdeal O) : ρ m = 0 := by
  by_contra h
  have hm' : algebraMap k O (ρ m)⁻¹ * m ∈ maximalIdeal O := Ideal.mul_mem_left _ _ hm
  have h1 : ρ (1 - algebraMap k O (ρ m)⁻¹ * m) = 0 := by
    rw [map_sub, map_one, map_mul, hρ, inv_mul_cancel₀ h, sub_self]
  have h2 : 1 - algebraMap k O (ρ m)⁻¹ * m ∈ maximalIdeal O := by
    by_contra h3
    have hu : IsUnit (1 - algebraMap k O (ρ m)⁻¹ * m) := by
      rwa [mem_maximalIdeal, mem_nonunits_iff, not_not] at h3
    exact (hu.map ρ).ne_zero h1
  have h4 := add_mem h2 hm'
  rw [sub_add_cancel] at h4
  exact (maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h4)

/-- THEOREM (proved). For every `a`, the difference `a - ρ(a)` lies in the maximal ideal.
Locator: a unit has a nonzero value under a ring homomorphism to a field. -/
theorem sub_retraction_mem (ρ : O →+* k) (hρ : ∀ c : k, ρ (algebraMap k O c) = c) (a : O) :
    a - algebraMap k O (ρ a) ∈ maximalIdeal O := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h := (hu.map ρ).ne_zero
  rw [map_sub, hρ, sub_self] at h
  exact h rfl

/-- THEOREM (proved). An element with value `1` under the retraction is a unit.
Locator: `retraction_eq_zero_of_mem`. -/
theorem isUnit_of_retraction_eq_one (ρ : O →+* k) (hρ : ∀ c : k, ρ (algebraMap k O c) = c)
    {u : O} (hu : ρ u = 1) : IsUnit u := by
  by_contra h
  have hm : u ∈ maximalIdeal O := (mem_maximalIdeal u).mpr h
  rw [retraction_eq_zero_of_mem ρ hρ hm] at hu
  exact zero_ne_one hu

/-- DEFINITION. The `k`-linear map `a ↦ (a - ρ(a)) mod 𝔪²` of `O` into its cotangent space.
Locator: Mathlib, `Ideal.toCotangent`. -/
def pointLinear (ρ : O →+* k) (hρ : ∀ c : k, ρ (algebraMap k O c) = c) :
    O →ₗ[k] CotangentSpace O where
  toFun a := (maximalIdeal O).toCotangent ⟨a - algebraMap k O (ρ a), sub_retraction_mem ρ hρ a⟩
  map_add' a b := by
    rw [← map_add]
    congr 1
    ext
    simp only [map_add, Submodule.coe_add]
    ring
  map_smul' c a := by
    rw [RingHom.id_apply]
    conv_rhs => rw [← algebraMap_smul O c, ← map_smul]
    congr 1
    ext
    simp only [Submodule.coe_smul, smul_eq_mul, Algebra.smul_def, map_mul, hρ]
    ring

/-- THEOREM (proved). The formula for `pointLinear`. Locator: `pointLinear`. -/
theorem pointLinear_apply (ρ : O →+* k) (hρ : ∀ c : k, ρ (algebraMap k O c) = c) (a : O) :
    pointLinear ρ hρ a =
      (maximalIdeal O).toCotangent ⟨a - algebraMap k O (ρ a), sub_retraction_mem ρ hρ a⟩ :=
  rfl

/-- DEFINITION. The derivation `a ↦ (a - ρ(a)) mod 𝔪²`: the Leibniz rule holds because
`ab - ρ(a)ρ(b) - a(b - ρ(b)) - b(a - ρ(a)) = -(a - ρ(a))(b - ρ(b)) ∈ 𝔪²`.
Locator: Hartshorne, II.8.7; Mathlib, `Derivation.mk'`. -/
def pointDerivation (ρ : O →+* k) (hρ : ∀ c : k, ρ (algebraMap k O c) = c) :
    Derivation k O (CotangentSpace O) :=
  Derivation.mk' (pointLinear ρ hρ) fun a b => by
    rw [pointLinear_apply, pointLinear_apply, pointLinear_apply, ← map_smul, ← map_smul,
      ← map_add, Ideal.toCotangent_eq]
    have h := Ideal.mul_mem_mul (sub_retraction_mem ρ hρ a) (sub_retraction_mem ρ hρ b)
    rw [← pow_two] at h
    convert neg_mem h using 1
    simp only [Submodule.coe_add, Submodule.coe_smul, smul_eq_mul, map_mul]
    ring

/-- DEFINITION. The evaluation of Kähler differentials at the rational point:
`Ω[O/k] → 𝔪/𝔪²`, `D a ↦ (a - a(P)) mod 𝔪²`. Locator: Mathlib,
`Derivation.liftKaehlerDifferential`; Hartshorne, II.8.7. -/
def pointEval (ρ : O →+* k) (hρ : ∀ c : k, ρ (algebraMap k O c) = c) :
    Ω[O⁄k] →ₗ[O] CotangentSpace O :=
  (pointDerivation ρ hρ).liftKaehlerDifferential

/-- THEOREM (proved). The evaluation of `D a` is the class of `a - a(P)`.
Locator: Mathlib, `Derivation.liftKaehlerDifferential_comp_D`. -/
theorem pointEval_D (ρ : O →+* k) (hρ : ∀ c : k, ρ (algebraMap k O c) = c) (a : O) :
    pointEval ρ hρ (D k O a) =
      (maximalIdeal O).toCotangent ⟨a - algebraMap k O (ρ a), sub_retraction_mem ρ hρ a⟩ :=
  Derivation.liftKaehlerDifferential_comp_D _ a

/-- THEOREM (proved). For `a` in the maximal ideal, the evaluation of `D a` is the class of `a`.
Locator: `pointEval_D`, `retraction_eq_zero_of_mem`. -/
theorem pointEval_D_of_mem (ρ : O →+* k) (hρ : ∀ c : k, ρ (algebraMap k O c) = c) {a : O}
    (ha : a ∈ maximalIdeal O) :
    pointEval ρ hρ (D k O a) = (maximalIdeal O).toCotangent ⟨a, ha⟩ := by
  rw [pointEval_D]
  congr 1
  ext
  simp [retraction_eq_zero_of_mem ρ hρ ha]

/-- THEOREM (proved). If `u` is a unit of value `1` and `a ∈ 𝔪`, then `u⁻¹ • D a` evaluates to the
class of `a`: `u⁻¹a - a = (u⁻¹ - 1)a ∈ 𝔪²`. Locator: `pointEval_D_of_mem`. -/
theorem pointEval_unit_inv_smul_D (ρ : O →+* k) (hρ : ∀ c : k, ρ (algebraMap k O c) = c)
    (u : Oˣ) (hu : ρ u = 1) {a : O} (ha : a ∈ maximalIdeal O) :
    pointEval ρ hρ ((↑u⁻¹ : O) • D k O a) = (maximalIdeal O).toCotangent ⟨a, ha⟩ := by
  rw [map_smul, pointEval_D_of_mem ρ hρ ha, ← map_smul, Ideal.toCotangent_eq]
  have hinv : ρ (↑u⁻¹ : O) = 1 := by
    have h := congrArg ρ u.inv_mul
    rwa [map_mul, hu, mul_one, map_one] at h
  have h1 : (↑u⁻¹ : O) - 1 ∈ maximalIdeal O := by
    have h := sub_retraction_mem ρ hρ (↑u⁻¹ : O)
    rwa [hinv, map_one] at h
  have h := Ideal.mul_mem_mul h1 ha
  rw [← pow_two] at h
  convert h using 1
  simp only [Submodule.coe_smul, smul_eq_mul]
  ring

end ZInQ.Contrib.RC53Assist.HodgeLineBinding
