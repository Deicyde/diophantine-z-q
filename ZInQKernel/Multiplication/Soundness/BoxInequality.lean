import Mathlib

/-!
# The final inequality of the finite-box deduction

Blueprint: `multiplication/soundness/box-inequality.md`.
-/

namespace ZInQ.Mult

/-- **The final inequality.** If `A ≥ 1` and `N² < 24 A N^(48/25) + 10` for an integer `N ≥ 0`,
then `N < (48 A)¹³`. -/
theorem box_inequality {A : ℝ} (hA : 1 ≤ A) (N : ℕ)
    (h : (N : ℝ) ^ 2 < 24 * A * (N : ℝ) ^ ((48 : ℝ) / 25) + 10) :
    (N : ℝ) < (48 * A) ^ 13 := by
  have h48 : (1 : ℝ) ≤ 48 * A := by linarith
  have hpow : (48 : ℝ) ≤ (48 * A) ^ 13 :=
    calc (48 : ℝ) ≤ 48 * A := by linarith
      _ = (48 * A) ^ 1 := (pow_one _).symm
      _ ≤ (48 * A) ^ 13 := pow_le_pow_right₀ h48 (by norm_num)
  rcases Nat.lt_or_ge N 5 with hN | hN
  · have : (N : ℝ) ≤ 4 := by exact_mod_cast Nat.lt_succ_iff.mp hN
    linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN5 : (5 : ℝ) ≤ N := by exact_mod_cast hN
  set u : ℝ := (N : ℝ) ^ ((2 : ℝ) / 25) with hu
  have hu0 : 0 ≤ u := by positivity
  -- `N² = N^(2/25) · N^(48/25)` and `N² = (N^(2/25))²⁵`.
  have hsplit : (N : ℝ) ^ 2 = u * (N : ℝ) ^ ((48 : ℝ) / 25) := by
    rw [hu, ← Real.rpow_add hN0]; norm_num
  have hu25 : (N : ℝ) ^ 2 = u ^ 25 := by
    rw [hu, ← Real.rpow_natCast ((N : ℝ) ^ ((2 : ℝ) / 25)) 25, ← Real.rpow_mul hN0.le]; norm_num
  have hlt : u < 48 * A := by
    by_contra hge
    replace hge := not_lt.mp hge
    have hv : 0 ≤ (N : ℝ) ^ ((48 : ℝ) / 25) := by positivity
    have : 24 * A * (N : ℝ) ^ ((48 : ℝ) / 25) ≤ (N : ℝ) ^ 2 / 2 := by
      rw [hsplit]; nlinarith
    nlinarith
  have h2 : (N : ℝ) ^ 2 < ((48 * A) ^ 13) ^ 2 := by
    rw [hu25, ← pow_mul]
    calc u ^ 25 < (48 * A) ^ 25 := pow_lt_pow_left₀ hlt hu0 (by norm_num)
      _ ≤ (48 * A) ^ (13 * 2) := pow_le_pow_right₀ h48 (by norm_num)
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h2

end ZInQ.Mult
