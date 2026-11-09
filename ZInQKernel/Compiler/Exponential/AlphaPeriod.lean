import ZInQKernel.Compiler.Exponential.AlphaMatrix
import ZInQ.AlphaPeriodReflection
import ZInQ.AlphaCompanionBound
import ZInQ.AlphaIndexCompanion
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Period and reflection modulo the companion

Blueprint: `compiler/natural/exponential/alpha-period.md`.

For `b > 2`, `m > 0` and the companion `v = U_{m+1} - U_{m-1} = tr(M_b^m) = b U_m - 2 U_{m-1}`:
folding of indices around multiples of `2m` (upstream `exists_folded_index`), the period and
reflection congruences (upstream `companion_dvd_alphaZ_add_period`,
`companion_dvd_alphaZ_reflection`), the signed residue of a folded index, and for `b > 3` the
bound `2 U_j < v` for `j ≤ m` (upstream `two_mul_alphaZ_lt_companion`).
-/

namespace ZInQ.AlphaPower

/-- The companion is `b U_m - 2 U_{m-1}`. -/
theorem companion_eq (b m : ℕ) (hm : 0 < m) :
    alphaZ b (m + 1) - alphaZ b (m - 1) = (b : ℤ) * alphaZ b m - 2 * alphaZ b (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel, alphaZ_add_two]
  ring

/-- The companion is the trace of `M_b^m`. -/
theorem companion_eq_trace (b m : ℕ) (hm : 0 < m) :
    (alphaMat b ^ m).trace = alphaZ b (m + 1) - alphaZ b (m - 1) := by
  rw [alphaMat_pow b m hm, Matrix.trace_fin_two]
  simp [sub_eq_add_neg]

/-- Folding: `n = 2lm + j` or `n = 2lm - j` with `0 < j < 2lm`, for some `l` and `j ≤ m`. -/
theorem alphaZ_fold_index (m n : ℕ) (hm : 0 < m) :
    ∃ l j : ℕ, j ≤ m ∧ (n = 2 * l * m + j ∨ (n = 2 * l * m - j ∧ 0 < j ∧ j < 2 * l * m)) :=
  exists_folded_index m n hm

/-- Period: `U_{j+2lm} ≡ (-1)^l U_j (mod v)`. -/
theorem alphaZ_period (b m j l : ℕ) (hb : 2 < b) :
    (alphaZ b (m + 1) - alphaZ b (m - 1)) ∣ alphaZ b (j + 2 * l * m) - (-1) ^ l * alphaZ b j :=
  companion_dvd_alphaZ_add_period b m j l hb

/-- Reflection: `U_{2lm-j} ≡ -(-1)^l U_j (mod v)` for `0 < j < 2lm`. -/
theorem alphaZ_reflection (b m j l : ℕ) (hb : 2 < b) (hj : 0 < j) (hjlt : j < 2 * l * m) :
    (alphaZ b (m + 1) - alphaZ b (m - 1)) ∣ alphaZ b (2 * l * m - j) - -((-1) ^ l * alphaZ b j) := by
  rw [sub_neg_eq_add]
  exact companion_dvd_alphaZ_reflection b m j l hb hj hjlt

/-- For a folded index, `U_n ≡ ± U_j (mod v)`. -/
theorem alphaZ_folded_residue (b m n l j : ℕ) (hb : 2 < b)
    (hf : n = 2 * l * m + j ∨ (n = 2 * l * m - j ∧ 0 < j ∧ j < 2 * l * m)) :
    (alphaZ b (m + 1) - alphaZ b (m - 1)) ∣ alphaZ b n - alphaZ b j ∨
      (alphaZ b (m + 1) - alphaZ b (m - 1)) ∣ alphaZ b n + alphaZ b j := by
  rcases hf with rfl | ⟨rfl, hj, hjlt⟩
  · have h := alphaZ_period b m j l hb
    rw [show 2 * l * m + j = j + 2 * l * m by ring]
    rcases neg_one_pow_eq_or ℤ l with hl | hl <;> rw [hl] at h
    · left; simpa using h
    · right; simpa using h
  · have h := companion_dvd_alphaZ_reflection b m j l hb hj hjlt
    rcases neg_one_pow_eq_or ℤ l with hl | hl <;> rw [hl] at h
    · right; simpa using h
    · left; simpa [sub_eq_add_neg] using h

/-- Bounds: for `b > 3`, `2 U_j < v` for every `j ≤ m`. -/
theorem two_mul_alphaZ_lt_companion' (b j m : ℕ) (hb : 3 < b) (hm : 0 < m) (hjm : j ≤ m) :
    2 * alphaZ b j < alphaZ b (m + 1) - alphaZ b (m - 1) :=
  two_mul_alphaZ_lt_companion b j m hb hm hjm

/-- In particular `v > 2 U_m` for `b > 3`. -/
theorem two_mul_alphaZ_lt_companion_self (b m : ℕ) (hb : 3 < b) (hm : 0 < m) :
    2 * alphaZ b m < alphaZ b (m + 1) - alphaZ b (m - 1) :=
  two_mul_alphaZ_lt_companion b m m hb hm le_rfl

end ZInQ.AlphaPower
