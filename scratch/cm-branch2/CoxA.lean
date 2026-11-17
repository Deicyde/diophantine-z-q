import Mathlib

/-! cm-branch2 scratch: Cox, Lemma 7.5, the elementary half: for `τ` with `Im τ > 0` and a primitive form
`aτ² + bτ + c = 0`, `a > 0`, the multipliers of `ℤ + ℤτ` are exactly `ℤ + ℤ(aτ)`. -/

namespace CoxA

/-- Coordinates in `ℤ + ℤτ` are unique when `Im τ ≠ 0`. -/
theorem coords_unique {τ : ℂ} (hτ : τ.im ≠ 0) {m n m' n' : ℝ}
    (h : (m : ℂ) + n * τ = m' + n' * τ) : m = m' ∧ n = n' := by
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  have hn : n = n' := by
    rcases mul_eq_mul_right_iff.mp him with h1 | h1
    · exact h1
    · exact absurd h1 hτ
  subst hn
  constructor <;> linarith

/-- **Cox, Lemma 7.5 (elementary half).** -/
theorem mult_iff {τ : ℂ} (hτ : 0 < τ.im) {a b c : ℤ} (ha : 0 < a)
    (hprim : Int.gcd (Int.gcd a b) c = 1) (hq : (a : ℂ) * τ ^ 2 + b * τ + c = 0) (m n : ℤ) :
    (∃ p q : ℤ, ((m : ℂ) + n * τ) * τ = p + q * τ) ↔ a ∣ n := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hτ2 : τ ^ 2 = (-(b : ℂ) * τ - c) / a := by
    field_simp; linear_combination hq
  constructor
  · rintro ⟨p, q, h⟩
    -- (m + nτ)τ = mτ + n(-bτ - c)/a, so  -nc/a = p, m - nb/a = q
    have h' : ((-(n * c : ℤ) : ℝ) / a : ℂ) + ((m * a - n * b : ℤ) / a : ℝ) * τ = (p : ℝ) + (q : ℝ) * τ := by
      have : ((m : ℂ) + n * τ) * τ = m * τ + n * τ ^ 2 := by ring
      rw [this, hτ2] at h
      push_cast
      rw [← h]
      field_simp
      ring
    obtain ⟨h1, h2⟩ := coords_unique hτ.ne' h'
    have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    have e1 : (-(n * c) : ℤ) = p * a := by
      have : ((-(n * c : ℤ) : ℝ)) = (p : ℝ) * a := by field_simp at h1; linarith
      exact_mod_cast this
    have e2 : (m * a - n * b : ℤ) = q * a := by
      have : ((m * a - n * b : ℤ) : ℝ) = (q : ℝ) * a := by field_simp at h2; linarith
      exact_mod_cast this
    have hc : a ∣ n * c := ⟨-p, by linarith⟩
    have hb : a ∣ n * b := ⟨m - q, by linarith⟩
    have hna : a ∣ n * a := dvd_mul_left a n
    -- gcd(a, b, c) = 1 ⇒ a ∣ n
    have hg : a ∣ n * (Int.gcd (Int.gcd a b) c : ℤ) := by
      rw [Int.gcd_eq_gcd_ab (Int.gcd a b : ℤ) c, ← Int.gcd_eq_gcd_ab]
      sorry
    simpa [hprim] using hg
  · rintro ⟨k, rfl⟩
    refine ⟨-(k * c), m - k * b, ?_⟩
    push_cast
    have : ((m : ℂ) + (a * k : ℤ) * τ) * τ = m * τ + k * ((a : ℂ) * τ ^ 2) := by push_cast; ring
    rw [this, show (a : ℂ) * τ ^ 2 = -(b : ℂ) * τ - c by linear_combination hq]
    ring

end CoxA
