import ZInQKernel.Assembly.Local.TestDivisibility
import ZInQ.RationalSeparation
import ZInQKernel.Hypotheses.HeightMin

/-!
# An accepting main branch forces the exact value

Blueprint: `assembly/main-branch-exactness.md`.

In an accepting main branch, Close gives `n ∉ 𝒞`, `κ ≠ 0` and `|t - n| < e^{-𝓑(n, κ)}`, and the
six local tests give `t ∉ 𝒞` and `M_{S_ht}(t) ∣ κ F(n)` (Lemma 11.1). As `κ F(n) ≠ 0`, the
six-contact estimate at `S = S_ht`, `R = D` gives `h(t) ≤ A⁽⁰⁾_ht M_{S_ht}(t)²⁴ ≤ 𝓑(n, κ)`, and a
rational number of height at most `𝓑` within `e^{-𝓑}` of an integer is that integer
(upstream `eq_int_of_real_abs_sub_lt_exp_neg_of_height_le`). The constants `A⁽⁰⁾_ht` and
`𝓑(n, κ)` are never evaluated.
-/

namespace ZInQ.Assembly

open Compiler.Precision

/-- The hypothesis file's height `h` is upstream's `rationalLogHeight`. -/
theorem ratHeight_eq_rationalLogHeight (q : ℚ) : ratHeight q = rationalLogHeight q := rfl

/-- **The height bound of an accepting main branch.** If `n ∉ 𝒞` and `Test(n, κ, t)`, then
`h(t) ≤ 𝓑(n, κ) = A⁽⁰⁾_ht |κ F(n)|²⁴`. -/
theorem ratHeight_le_bound_of_test (hH : SixContactMin) {n κ : ℤ} {t : ℚ}
    (hn : n ∉ contacts) (hT : Test n κ t) : ratHeight t ≤ (bound n κ : ℝ) := by
  have hdvd := test_dvd hT
  obtain ⟨hκ, ht, -⟩ := hT
  have hne : (κ * sixF n).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact mul_ne_zero hκ fun h => hn ((sixF_eq_zero_iff n).1 h)
  have hle : contactSupport heightPrimes t ≤ (κ * sixF n).natAbs :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
  refine (sixContact_at_heightPrimes hH ht).trans ?_
  rw [bound, Nat.cast_mul, Nat.cast_pow]
  gcongr

/-- **Exactness from closeness and the six local tests.** If `n ∉ 𝒞`,
`|t - n| < e^{-𝓑(n, κ)}` in `ℝ` and `Test(n, κ, t)`, then `t = n`. -/
theorem eq_of_close_of_test (hH : SixContactMin) {n κ : ℤ} {t : ℚ} (hn : n ∉ contacts)
    (hclose : |(t : ℝ) - n| < Real.exp (-(bound n κ : ℝ))) (hT : Test n κ t) : t = n :=
  eq_int_of_real_abs_sub_lt_exp_neg_of_height_le t n _
    ((ratHeight_eq_rationalLogHeight t).symm ▸ ratHeight_le_bound_of_test hH hn hT) hclose

end ZInQ.Assembly
