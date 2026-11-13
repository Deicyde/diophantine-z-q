import Mathlib

/-!
# Character sums and summation by parts

Plan step 1 (first half), `docs/effective-dirichlet-plan.md`.

* `ZInQ.Progressions.norm_sum_Ico_char_le`: a sum of a nontrivial Dirichlet character
  `χ` mod `q` over any interval of consecutive naturals has norm at most `q`;
* `ZInQ.Progressions.norm_sum_char_le`: hence `‖∑_{0 < n ≤ x} χ n‖ ≤ q` for every real `x`;
* `ZInQ.Progressions.norm_sum_mul_antitone_le`: discrete summation by parts against a
  nonnegative nonincreasing weight.
-/

open Finset

namespace ZInQ.Progressions

variable {q : ℕ} [NeZero q]

/-- Over `q` consecutive naturals, the values of `χ` run once through `ZMod q`. -/
theorem sum_Ico_char_period_eq (χ : DirichletCharacter ℂ q) (a : ℕ) :
    ∑ n ∈ Ico a (a + q), χ n = ∑ x : ZMod q, χ x := by
  rw [Finset.sum_Ico_eq_sum_range, add_tsub_cancel_left]
  refine Finset.sum_nbij' (fun i ↦ ((a + i : ℕ) : ZMod q)) (fun x ↦ (x - a).val) ?_ ?_ ?_ ?_ ?_
  · intro i _; exact Finset.mem_univ _
  · intro x _; exact Finset.mem_range.mpr (ZMod.val_lt _)
  · intro i hi
    have hi' : i < q := Finset.mem_range.mp hi
    simp only [Nat.cast_add, add_sub_cancel_left, ZMod.val_natCast, Nat.mod_eq_of_lt hi']
  · intro x _
    simp only [Nat.cast_add, ZMod.natCast_val, ZMod.cast_id', id_eq, add_sub_cancel]
  · intro i _; simp

/-- For `χ ≠ 1` the sum over a full period vanishes. -/
theorem sum_Ico_char_period_eq_zero {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (a : ℕ) :
    ∑ n ∈ Ico a (a + q), χ n = 0 := by
  rw [sum_Ico_char_period_eq, MulChar.sum_eq_zero_of_ne_one hχ]

/-- A sum of a nontrivial character over an interval of consecutive naturals has norm
at most `q`. -/
theorem norm_sum_Ico_char_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (a b : ℕ) :
    ‖∑ n ∈ Ico a b, χ n‖ ≤ q := by
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    by_cases hb : a + q ≤ b
    · have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
      have h1 : a ≤ b - q := by omega
      have h2 : b - q ≤ b := Nat.sub_le b q
      rw [← Finset.sum_Ico_consecutive _ h1 h2]
      have h3 : ∑ n ∈ Ico (b - q) b, χ n = 0 := by
        have := sum_Ico_char_period_eq_zero hχ (b - q)
        rwa [Nat.sub_add_cancel (by omega : q ≤ b)] at this
      rw [h3, add_zero]
      exact ih (b - q) (by omega)
    · calc ‖∑ n ∈ Ico a b, χ n‖ ≤ ∑ n ∈ Ico a b, ‖χ n‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Ico a b, (1 : ℝ) := Finset.sum_le_sum fun n _ ↦ DirichletCharacter.norm_le_one χ n
        _ = (b - a : ℕ) := by simp
        _ ≤ q := by exact_mod_cast (by omega : b - a ≤ q)

/-- Plan step 1: `|∑_{n ≤ x} χ(n)| ≤ q` for a nontrivial character and every real `x`. -/
theorem norm_sum_char_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (x : ℝ) :
    ‖∑ n ∈ Ioc 0 ⌊x⌋₊, χ n‖ ≤ q := by
  rw [← Finset.Ico_add_one_add_one_eq_Ioc]
  exact norm_sum_Ico_char_le hχ _ _

/-- The interval form used by summation by parts. -/
theorem norm_sum_Ioc_char_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (a b : ℕ) :
    ‖∑ n ∈ Ioc a b, χ n‖ ≤ q := by
  rw [← Finset.Ico_add_one_add_one_eq_Ioc]
  exact norm_sum_Ico_char_le hχ _ _

/-- Summation by parts: if every partial sum `∑_{N < n ≤ m} c n` has norm at most `B` and `f`
is nonnegative and nonincreasing from `N + 1` on, then `‖∑_{N < n ≤ K} c n f n‖ ≤ B f (N + 1)`. -/
theorem norm_sum_mul_antitone_le (c : ℕ → ℂ) (f : ℕ → ℝ) {N : ℕ} {B : ℝ}
    (hB : ∀ m, ‖∑ n ∈ Ioc N m, c n‖ ≤ B)
    (hf0 : ∀ n, N + 1 ≤ n → 0 ≤ f n) (hf : ∀ n, N + 1 ≤ n → f (n + 1) ≤ f n) (K : ℕ) :
    ‖∑ n ∈ Ioc N K, c n * f n‖ ≤ B * f (N + 1) := by
  rcases le_or_gt K N with hK | hK
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]
    exact mul_nonneg ((norm_nonneg _).trans (hB 0)) (hf0 _ le_rfl)
  -- The invariant: `‖∑_{N<n≤K} c n f n - C(K) f(K+1)‖ ≤ B (f(N+1) - f(K+1))`.
  have key : ∀ K, N ≤ K →
      ‖∑ n ∈ Ioc N K, c n * f n - (∑ n ∈ Ioc N K, c n) * (f (K + 1) : ℂ)‖ ≤
        B * (f (N + 1) - f (K + 1)) := by
    intro K hK
    induction K, hK using Nat.le_induction with
    | base => simp
    | succ K hK ih =>
      rw [Finset.sum_Ioc_succ_top (by omega), Finset.sum_Ioc_succ_top (by omega)]
      have e : ∑ n ∈ Ioc N K, c n * f n + c (K + 1) * f (K + 1) -
            (∑ n ∈ Ioc N K, c n + c (K + 1)) * (f (K + 1 + 1) : ℂ) =
          (∑ n ∈ Ioc N K, c n * f n - (∑ n ∈ Ioc N K, c n) * (f (K + 1) : ℂ)) +
            (∑ n ∈ Ioc N (K + 1), c n) * ((f (K + 1) - f (K + 1 + 1) : ℝ) : ℂ) := by
        rw [Finset.sum_Ioc_succ_top (by omega)]; push_cast; ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr (hf _ (by omega)))]
      have := mul_le_mul_of_nonneg_right (hB (K + 1)) (sub_nonneg.mpr (hf (K + 1) (by omega)))
      nlinarith
  have hk := key K hK.le
  have hfK : 0 ≤ f (K + 1) := hf0 _ (by omega)
  calc ‖∑ n ∈ Ioc N K, c n * f n‖
      ≤ ‖∑ n ∈ Ioc N K, c n * f n - (∑ n ∈ Ioc N K, c n) * (f (K + 1) : ℂ)‖ +
          ‖(∑ n ∈ Ioc N K, c n) * (f (K + 1) : ℂ)‖ := norm_le_norm_sub_add _ _
    _ ≤ B * (f (N + 1) - f (K + 1)) + B * f (K + 1) := by
        refine add_le_add hk ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hfK]
        exact mul_le_mul_of_nonneg_right (hB K) hfK
    _ = B * f (N + 1) := by ring

end ZInQ.Progressions
