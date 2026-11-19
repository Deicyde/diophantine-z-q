import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Strict relative displacement excludes unit-length cycles

The finite telescoping sum of a scalar displacement is zero on a finite
cycle. Every summand differs from the original displacement by strictly
smaller valuation. If the cycle length has valuation one, comparison
with that many copies of the displacement forces it to vanish.
-/

noncomputable section
set_option autoImplicit false

open scoped BigOperators

namespace WildTrace

variable {K Ω Γ₀ : Type*} [Field K] [Field Ω] [Algebra K Ω]
  [LinearOrderedCommGroupWithZero Γ₀] [Nontrivial Γ₀]

/-- Strict relative displacement implies preservation of the actual valuation. -/
theorem valuation_apply_eq (v : Valuation Ω Γ₀) (σ : Ω ≃ₐ[K] Ω)
    (hσ : ∀ x : Ω, x ≠ 0 → v (σ x - x) < v x) (x : Ω) : v (σ x) = v x := by
  by_cases hx : x = 0
  · simp [hx]
  · exact v.map_eq_of_sub_lt (hσ x hx)

/-- Every natural iterate has the same valuation on every field element. -/
theorem valuation_iterate_eq (v : Valuation Ω Γ₀) (σ : Ω ≃ₐ[K] Ω)
    (hσ : ∀ x : Ω, x ≠ 0 → v (σ x - x) < v x) (n : ℕ) (x : Ω) :
    v ((σ : Ω → Ω)^[n] x) = v x := by
  induction n with
  | zero => rfl
  | succ n hn => rw [Function.iterate_succ_apply', valuation_apply_eq v σ hσ, hn]

/-- Every natural iterate satisfies the same strictly small displacement condition. -/
theorem iterate_displacement_lt (v : Valuation Ω Γ₀) (σ : Ω ≃ₐ[K] Ω)
    (hσ : ∀ x : Ω, x ≠ 0 → v (σ x - x) < v x) (n : ℕ) (x : Ω) (hx : x ≠ 0) :
    v ((σ : Ω → Ω)^[n] x - x) < v x := by
  induction n with
  | zero => simpa using (v.pos_iff.mpr hx)
  | succ n hn =>
      have hval := valuation_iterate_eq v σ hσ n x
      have hne : (σ : Ω → Ω)^[n] x ≠ 0 := by
        intro hz
        rw [hz, map_zero] at hval
        exact (v.ne_zero_iff.mpr hx) hval.symm
      have hsmall := hσ ((σ : Ω → Ω)^[n] x) hne
      rw [hval] at hsmall
      have he : (σ : Ω → Ω)^[n + 1] x - x =
          (σ ((σ : Ω → Ω)^[n] x) - (σ : Ω → Ω)^[n] x) +
            ((σ : Ω → Ω)^[n] x - x) := by
        rw [Function.iterate_succ_apply']
        ring
      rw [he]
      exact v.map_add_lt hsmall hn

/-- The actual algebra automorphism power equals its function iterate. -/
theorem algEquiv_pow_apply (σ : Ω ≃ₐ[K] Ω) (n : ℕ) (x : Ω) :
    (σ ^ n) x = (σ : Ω → Ω)^[n] x := by
  induction n with
  | zero => rfl
  | succ n hn => simp only [pow_succ', AlgEquiv.mul_apply, Function.iterate_succ_apply', hn]

/-- The strict displacement condition is preserved under every automorphism power. -/
theorem pow_displacement_lt (v : Valuation Ω Γ₀) (σ : Ω ≃ₐ[K] Ω)
    (hσ : ∀ x : Ω, x ≠ 0 → v (σ x - x) < v x) (n : ℕ) :
    ∀ x : Ω, x ≠ 0 → v ((σ ^ n) x - x) < v x := by
  intro x hx
  rw [algEquiv_pow_apply]
  exact iterate_displacement_lt v σ hσ n x hx

/-- Successive scalar displacements have a genuine finite telescoping sum. -/
theorem sum_iterate_displacement (σ : Ω ≃ₐ[K] Ω) (r : ℕ) (x : Ω) :
    (∑ i ∈ Finset.range r, (σ : Ω → Ω)^[i] (σ x - x)) =
      (σ : Ω → Ω)^[r] x - x := by
  induction r with
  | zero => simp
  | succ r hr =>
      rw [Finset.sum_range_succ, hr]
      have hmap : (σ : Ω → Ω)^[r] (σ x - x) =
          (σ : Ω → Ω)^[r] (σ x) - (σ : Ω → Ω)^[r] x := by
        rw [← algEquiv_pow_apply σ r (σ x - x), ← algEquiv_pow_apply σ r (σ x),
          ← algEquiv_pow_apply σ r x]
        exact map_sub (σ ^ r) (σ x) x
      rw [hmap, ← Function.iterate_succ_apply]
      ring

/-- A scalar cycle of valuation-unit length is actually a fixed point. -/
theorem fixed_of_unit_period (v : Valuation Ω Γ₀) (σ : Ω ≃ₐ[K] Ω)
    (hσ : ∀ x : Ω, x ≠ 0 → v (σ x - x) < v x)
    (r : ℕ) (hr : v (r : Ω) = 1) (x : Ω)
    (hperiod : (σ : Ω → Ω)^[r] x = x) : σ x = x := by
  by_contra hfix
  let z : Ω := σ x - x
  have hz : z ≠ 0 := sub_ne_zero.mpr hfix
  have hs : (∑ i ∈ Finset.range r, (σ : Ω → Ω)^[i] z) = 0 := by
    change (∑ i ∈ Finset.range r, (σ : Ω → Ω)^[i] (σ x - x)) = 0
    rw [sum_iterate_displacement, hperiod, sub_self]
  have hsmall : v (∑ i ∈ Finset.range r, ((σ : Ω → Ω)^[i] z - z)) < v z :=
    v.map_sum_lt (v.ne_zero_iff.mpr hz) (fun i _ => iterate_displacement_lt v σ hσ i z hz)
  have he : (∑ i ∈ Finset.range r, ((σ : Ω → Ω)^[i] z - z)) = -(r : Ω) * z := by
    rw [Finset.sum_sub_distrib, hs, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [he, v.map_mul, Valuation.map_neg, hr, one_mul] at hsmall
  exact lt_irrefl _ hsmall

/-- A finite-order actual field automorphism has order prime to every
prime whose scalar is a valuation unit. -/
theorem orderOf_coprime_unit_prime (v : Valuation Ω Γ₀) (σ : Ω ≃ₐ[K] Ω)
    (hσ : ∀ x : Ω, x ≠ 0 → v (σ x - x) < v x)
    (hfinite : IsOfFinOrder σ) (ℓ : ℕ) (hℓ : ℓ.Prime) (hu : v (ℓ : Ω) = 1) :
    Nat.Coprime (orderOf σ) ℓ := by
  apply Nat.Coprime.symm
  apply (hℓ.coprime_iff_not_dvd).2
  intro hdiv
  let τ : Ω ≃ₐ[K] Ω := σ ^ (orderOf σ / ℓ)
  have hord : orderOf τ = ℓ := orderOf_pow_orderOf_div hfinite.orderOf_pos.ne' hdiv
  have ht : τ ^ ℓ = 1 := by rw [← hord]; exact pow_orderOf_eq_one τ
  have hτsmall := pow_displacement_lt v σ hσ (orderOf σ / ℓ)
  have hτone : τ = 1 := by
    ext x
    apply fixed_of_unit_period v τ hτsmall ℓ hu x
    rw [← algEquiv_pow_apply, ht]
    rfl
  have hbad : ℓ = 1 := by simpa only [hτone, orderOf_one] using hord.symm
  exact hℓ.ne_one hbad

end WildTrace
