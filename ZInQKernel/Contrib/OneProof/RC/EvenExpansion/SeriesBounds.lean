import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic

/-! Absolute convergence on the positive square shell. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenExpansion

/-- A series supported at the indices `j * (k + 1)^2`, with coefficients
of absolute value at most `k + 1`, is summable for every `‖q‖ < 1`. -/
theorem summable_squareShell {j : ℕ} (hj : 0 < j) (a : ℕ → ℂ)
    (hoff : ∀ n, (¬ ∃ k : ℕ, j * (k + 1) ^ 2 = n) → a n = 0)
    (hle : ∀ k : ℕ, ‖a (j * (k + 1) ^ 2)‖ ≤ ((k + 1 : ℕ) : ℝ))
    {q : ℂ} (hq : ‖q‖ < 1) : Summable (fun n => a n * q ^ n) := by
  let e (k : ℕ) := j * (k + 1) ^ 2
  have hei : Function.Injective e := by
    intro k l h
    exact Nat.succ_injective (Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0)
      (Nat.eq_of_mul_eq_mul_left hj h))
  have hzero (n : ℕ) (hn : n ∉ Set.range e) : a n * q ^ n = 0 := by
    rw [hoff n hn, zero_mul]
  apply (hei.summable_iff hzero).mp
  apply Summable.of_norm
  have hs := (summable_nat_add_iff 1).2 (summable_norm_pow_mul_geometric_of_norm_lt_one 1 hq)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) hs
  have hp : k + 1 ≤ e k := by
    calc
      k + 1 ≤ (k + 1) ^ 2 := by simp [pow_two]
      _ ≤ e k := Nat.le_mul_of_pos_left _ hj
  change ‖a (e k) * q ^ e k‖ ≤ ‖((k + 1 : ℕ) : ℂ) ^ 1 * q ^ (k + 1)‖
  simp only [norm_mul, norm_pow, pow_one, Complex.norm_natCast]
  exact mul_le_mul (hle k) (pow_le_pow_of_le_one (norm_nonneg _) hq.le hp)
    (pow_nonneg (norm_nonneg _) _) (Nat.cast_nonneg _)


end ZInQ.Manuscript.RC.EvenExpansion
