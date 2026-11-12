import Mathlib

/-!
# glue-vigneras: local normalizers of the maximal order of `B = (2,-3)` at `p = 2, 3`

`B_p = ℍ[ℚ_[p], 2, 0, -3]`, `𝒪_p` = the `ℤ_p`-span of N5's basis `(1, i, (1+j)/2, (i+ij)/2)`.
-/

open Quaternion

namespace GlueVigneras

section Unit
variable {p : ℕ} [hp : Fact p.Prime]

theorem norm_eq_one_of_toZMod_ne {z : ℤ_[p]} (h : PadicInt.toZMod z ≠ 0) : ‖z‖ = 1 := by
  by_contra hne
  have hlt : ‖z‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one z) hne
  have hm : z ∈ IsLocalRing.maximalIdeal ℤ_[p] := PadicInt.mem_nonunits.mpr hlt
  rw [← PadicInt.ker_toZMod] at hm
  exact h (RingHom.mem_ker.mp hm)

/-- A nonzero `p`-adic number has norm an integer power of `p`. -/
theorem norm_zpow {x : ℚ_[p]} (hx : x ≠ 0) : ∃ m : ℤ, ‖x‖ = (p : ℝ) ^ m :=
  ⟨_, Padic.norm_eq_zpow_neg_valuation hx⟩

theorem norm_zero_or_zpow (x : ℚ_[p]) : ‖x‖ = 0 ∨ ∃ m : ℤ, ‖x‖ = (p : ℝ) ^ m := by
  by_cases hx : x = 0
  · left; simp [hx]
  · right; exact norm_zpow hx

theorem max_zero_or_zpow (x y : ℚ_[p]) :
    max ‖x‖ ‖y‖ = 0 ∨ ∃ m : ℤ, max ‖x‖ ‖y‖ = (p : ℝ) ^ m := by
  rcases le_total ‖x‖ ‖y‖ with h | h
  · rw [max_eq_right h]; exact norm_zero_or_zpow y
  · rw [max_eq_left h]; exact norm_zero_or_zpow x

/-- A homogeneous binary quadratic form whose dehomogenizations take unit values on `ℤ_p` has
`‖Q x y‖ = max(‖x‖, ‖y‖)²`. -/
theorem norm_binary (Q : ℚ_[p] → ℚ_[p] → ℚ_[p])
    (hom : ∀ s x y, Q (s * x) (s * y) = s ^ 2 * Q x y)
    (h1 : ∀ t : ℚ_[p], ‖t‖ ≤ 1 → ‖Q 1 t‖ = 1) (h2 : ∀ t : ℚ_[p], ‖t‖ ≤ 1 → ‖Q t 1‖ = 1)
    (x y : ℚ_[p]) : ‖Q x y‖ = (max ‖x‖ ‖y‖) ^ 2 := by
  rcases le_total ‖y‖ ‖x‖ with h | h
  · rw [max_eq_left h]
    by_cases hx : x = 0
    · have hy : y = 0 := by simpa [hx] using h
      have := hom 0 0 0
      simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
      simp [hx, hy, this]
    · have hxn : ‖x‖ ≠ 0 := by simpa using hx
      have e : Q x y = x ^ 2 * Q 1 (y / x) := by
        rw [← hom]; congr 1 <;> field_simp
      rw [e, norm_mul, norm_pow, h1 _ (by rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _))]
      ring
  · rw [max_eq_right h]
    by_cases hy : y = 0
    · have hx : x = 0 := by simpa [hy] using h
      have := hom 0 0 0
      simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
      simp [hx, hy, this]
    · have e : Q x y = y ^ 2 * Q (x / y) 1 := by
        rw [← hom]; congr 1 <;> field_simp
      rw [e, norm_mul, norm_pow, h2 _ (by rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _))]
      ring

/-- Lift a `p`-adic number of norm `≤ 1` to `ℤ_p`. -/
def lift (t : ℚ_[p]) (ht : ‖t‖ ≤ 1) : ℤ_[p] := ⟨t, ht⟩

theorem coe_lift (t : ℚ_[p]) (ht : ‖t‖ ≤ 1) : ((lift t ht : ℤ_[p]) : ℚ_[p]) = t := rfl

@[simp] theorem coe_two : ((2 : ℤ_[p]) : ℚ_[p]) = 2 := by
  have := PadicInt.coe_natCast (p := p) 2; simpa using this

end Unit

/-- At `p = 3`: `‖a² - 2b²‖ = max(‖a‖,‖b‖)²` (2 is not a square mod 3). -/
theorem norm_form3 (a b : ℚ_[3]) : ‖a ^ 2 - 2 * b ^ 2‖ = (max ‖a‖ ‖b‖) ^ 2 := by
  apply norm_binary (fun x y => x ^ 2 - 2 * y ^ 2) (fun s x y => by ring)
  · intro t ht
    have e : (1 : ℚ_[3]) ^ 2 - 2 * t ^ 2 = ((1 - 2 * (lift t ht) ^ 2 : ℤ_[3]) : ℚ_[3]) := by
      push_cast [coe_lift, coe_two]; ring
    rw [e, ← PadicInt.norm_def]
    apply norm_eq_one_of_toZMod_ne
    rw [map_sub, map_one, map_mul, map_pow, map_ofNat]
    generalize PadicInt.toZMod (lift t ht) = s
    revert s; decide
  · intro t ht
    have e : t ^ 2 - 2 * (1 : ℚ_[3]) ^ 2 = (((lift t ht) ^ 2 - 2 : ℤ_[3]) : ℚ_[3]) := by
      push_cast [coe_lift, coe_two]; ring
    rw [e, ← PadicInt.norm_def]
    apply norm_eq_one_of_toZMod_ne
    rw [map_sub, map_pow, map_ofNat]
    generalize PadicInt.toZMod (lift t ht) = s
    revert s; decide

/-- At `p = 2`: `‖x² + xy + y²‖ = max(‖x‖,‖y‖)²` (the norm form of `ℤ₂[ω]`). -/
theorem norm_form2 (a b : ℚ_[2]) : ‖a ^ 2 + a * b + b ^ 2‖ = (max ‖a‖ ‖b‖) ^ 2 := by
  apply norm_binary (fun x y => x ^ 2 + x * y + y ^ 2) (fun s x y => by ring)
  · intro t ht
    have e : (1 : ℚ_[2]) ^ 2 + 1 * t + t ^ 2 = ((1 + (lift t ht) + (lift t ht) ^ 2 : ℤ_[2]) : ℚ_[2]) := by
      push_cast [coe_lift, coe_two]; ring
    rw [e, ← PadicInt.norm_def]
    apply norm_eq_one_of_toZMod_ne
    rw [map_add, map_add, map_one, map_pow]
    generalize PadicInt.toZMod (lift t ht) = s
    revert s; decide
  · intro t ht
    have e : t ^ 2 + t * 1 + (1 : ℚ_[2]) ^ 2 = (((lift t ht) ^ 2 + (lift t ht) + 1 : ℤ_[2]) : ℚ_[2]) := by
      push_cast [coe_lift, coe_two]; ring
    rw [e, ← PadicInt.norm_def]
    apply norm_eq_one_of_toZMod_ne
    rw [map_add, map_add, map_one, map_pow]
    generalize PadicInt.toZMod (lift t ht) = s
    revert s; decide

end GlueVigneras
