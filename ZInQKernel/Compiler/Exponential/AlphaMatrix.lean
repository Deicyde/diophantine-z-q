import ZInQKernel.Compiler.Exponential.AlphaSequence
import ZInQ.AlphaAddition
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Coprime.Basic

/-!
# Matrix powers and the quadratic identity

Blueprint: `compiler/natural/exponential/alpha-matrix.md`.

For every natural `b`: `M_b^n = !![U_{n+1}, -U_n; U_n, -U_{n-1}]` (`n ≥ 1`) with determinant one;
the quadratic identity `U_n² + U_{n+1}² - b U_n U_{n+1} = 1` (upstream `alphaZ_cassini`); adjacent
terms are coprime and not both even; and the addition formula (upstream `alphaZ_add_succ`).
-/

namespace ZInQ.AlphaPower

/-- `M_b^n = !![U_{n+1}, -U_n; U_n, -U_{n-1}]` for `n ≥ 1`. -/
theorem alphaMat_pow (b n : ℕ) (hn : 1 ≤ n) :
    alphaMat b ^ n =
      !![alphaZ b (n + 1), -alphaZ b n; alphaZ b n, -alphaZ b (n - 1)] := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [pow_one, alphaMat, alphaZ_add_two, alphaZ_one, alphaZ_zero]
    simp
  | succ n hn ih =>
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ, ih, alphaMat, Matrix.mul_fin_two]
    simp only [Nat.add_sub_cancel, show k + 1 + 1 + 1 = (k + 1) + 2 from rfl,
      show k + 1 + 1 = k + 2 from rfl, alphaZ_add_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring

theorem alphaMat_det (b : ℕ) : (alphaMat b).det = 1 := by
  simp [alphaMat, Matrix.det_fin_two_of]

/-- `det M_b^n = 1`. -/
theorem alphaMat_pow_det (b n : ℕ) : (alphaMat b ^ n).det = 1 := by
  rw [Matrix.det_pow, alphaMat_det, one_pow]

/-- The quadratic identity `U_n² + U_{n+1}² - b U_n U_{n+1} = 1`, for every natural `b`. -/
theorem alphaZ_quadratic (b n : ℕ) :
    alphaZ b n ^ 2 + alphaZ b (n + 1) ^ 2 - (b : ℤ) * alphaZ b n * alphaZ b (n + 1) = 1 :=
  alphaZ_cassini b n

/-- The quadratic identity in the form `U_n² - b U_n U_{n-1} + U_{n-1}² = 1`, `n ≥ 1`. -/
theorem alphaZ_quadratic_pred (b n : ℕ) (hn : 1 ≤ n) :
    alphaZ b n ^ 2 - (b : ℤ) * alphaZ b n * alphaZ b (n - 1) + alphaZ b (n - 1) ^ 2 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  linear_combination alphaZ_cassini b k

/-- Adjacent alpha values are coprime in `ℤ`, for every natural `b`. -/
theorem alphaZ_isCoprime_succ (b n : ℕ) : IsCoprime (alphaZ b n) (alphaZ b (n + 1)) :=
  ⟨alphaZ b n - (b : ℤ) * alphaZ b (n + 1), alphaZ b (n + 1), by
    linear_combination alphaZ_cassini b n⟩

/-- Adjacent alpha values are not both even. -/
theorem alphaZ_not_both_even (b n : ℕ) : ¬ (2 ∣ alphaZ b n ∧ 2 ∣ alphaZ b (n + 1)) := by
  rintro ⟨h0, h1⟩
  have h := (alphaZ_isCoprime_succ b n).isUnit_of_dvd' h0 h1
  rw [Int.isUnit_iff] at h
  omega

/-- The addition formula `U_{m+n+1} = U_{m+1} U_{n+1} - U_m U_n`. -/
theorem alphaZ_addition (b m n : ℕ) :
    alphaZ b (m + n + 1) = alphaZ b (m + 1) * alphaZ b (n + 1) - alphaZ b m * alphaZ b n :=
  alphaZ_add_succ b m n

end ZInQ.AlphaPower
