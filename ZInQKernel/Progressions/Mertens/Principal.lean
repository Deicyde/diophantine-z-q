import ZInQKernel.Progressions.Mertens.First
import ZInQKernel.Progressions.Mertens.Defs
import ZInQKernel.Progressions.Mertens.PrimePowers

/-!
# The principal character (plan step 4.3, main term)

`S_{χ₀}(x) − S_{χ₀}(y) ≥ log(x/y) − 2C₀ − log q` for `1 ≤ y ≤ x`, with `C₀ = 3` from Mertens'
first theorem: `S_{χ₀}` differs from `S` by the terms with `gcd(n, q) > 1`, which total at most
`log q`.
-/

namespace ZInQ.Progressions

open Finset Real
open ArithmeticFunction hiding log

variable {q : ℕ}

/-- `S_{χ₀}(x) = Σ_{n ≤ x, gcd(n, q) = 1} Λ(n)/n`. -/
lemma twistedSum_one_eq (x : ℝ) :
    twistedSum (1 : DirichletCharacter ℂ q) x =
      ((∑ n ∈ Ioc 0 ⌊x⌋₊ with n.Coprime q, Λ n / n : ℝ) : ℂ) := by
  rw [twistedSum, sum_filter]
  push_cast
  refine sum_congr rfl fun n _ ↦ ?_
  split_ifs with h
  · rw [MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr h), one_mul]; push_cast; ring
  · rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime]), zero_mul, zero_div]; simp

/-- `S(x) = S_{χ₀}(x) + Σ_{n ≤ x, gcd(n, q) > 1} Λ(n)/n`. -/
lemma mertensSum_eq_coprime_add_nonunit (x : ℝ) :
    mertensSum x = (∑ n ∈ Ioc 0 ⌊x⌋₊ with n.Coprime q, Λ n / n) +
      ∑ n ∈ Ioc 0 ⌊x⌋₊ with ¬ n.Coprime q, Λ n / n :=
  (sum_filter_add_sum_filter_not _ _ _).symm

/-- **The principal character**: for `1 ≤ y ≤ x`,
`S_{χ₀}(x) − S_{χ₀}(y) ≥ log(x/y) − 2C₀ − log q` with `C₀ = 3`. -/
theorem log_div_sub_le_re_twistedSum_one_sub [NeZero q] {x y : ℝ} (hy : 1 ≤ y) (hyx : y ≤ x) :
    Real.log (x / y) - 2 * 3 - Real.log q ≤
      (twistedSum (1 : DirichletCharacter ℂ q) x -
        twistedSum (1 : DirichletCharacter ℂ q) y).re := by
  rw [twistedSum_one_eq, twistedSum_one_eq, ← Complex.ofReal_sub, Complex.ofReal_re]
  have hx := mertensSum_eq_coprime_add_nonunit (q := q) x
  have hy' := mertensSum_eq_coprime_add_nonunit (q := q) y
  have h1 := sum_nonunit_vonMangoldt_div_le_log (NeZero.ne q) ⌊x⌋₊
  have h2 : 0 ≤ ∑ n ∈ Ioc 0 ⌊y⌋₊ with ¬ n.Coprime q, Λ n / n :=
    sum_nonneg fun _ _ ↦ div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
  have h3 := log_sub_two_le_mertensSum (hy.trans hyx)
  have h4 := mertensSum_le_log_add_three hy
  rw [log_div (by linarith) (by linarith)]
  linarith

end ZInQ.Progressions
