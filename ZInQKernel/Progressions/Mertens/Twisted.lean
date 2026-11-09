import ZInQKernel.Progressions.Mertens.Defs

/-!
# Twisted sums against `L(1, χ)` (plan step 4.2)

With `T(x) = Σ_{n ≤ x} χ(n) log n / n` and `log n = Σ_{d ∣ n} Λ(d)`,
`T(x) = Σ_{d ≤ x} χ(d) Λ(d)/d · Σ_{m ≤ x/d} χ(m)/m`. If the partial sums of `χ(m)/m` are within
`2q/y` of `L(1, χ)`, then `‖L(1, χ)‖ · ‖S_χ(x)‖ ≤ ‖T(x)‖ + 2q ψ(x)/x`.
-/

namespace ZInQ.Progressions

open Finset
open ArithmeticFunction hiding log
open scoped Chebyshev

variable {q : ℕ}

/-- The arithmetic function `n ↦ χ(n) Λ(n) / n`. -/
noncomputable def twistedVonMangoldtDiv (χ : DirichletCharacter ℂ q) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ χ n * Λ n / n, by simp⟩

/-- The arithmetic function `n ↦ χ(n) / n`. -/
noncomputable def charDivArith (χ : DirichletCharacter ℂ q) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ χ n / n, by simp⟩

lemma twistedVonMangoldtDiv_mul_charDiv (χ : DirichletCharacter ℂ q) (n : ℕ) :
    (twistedVonMangoldtDiv χ * charDivArith χ) n = χ n * Real.log n / n := by
  rw [mul_apply]
  have h : ∀ x ∈ n.divisorsAntidiagonal,
      twistedVonMangoldtDiv χ x.1 * charDivArith χ x.2 = χ n / n * (Λ x.1 : ℂ) := by
    intro x hx
    rw [Nat.mem_divisorsAntidiagonal] at hx
    obtain ⟨rfl, hn⟩ := hx
    have h1 : (x.1 : ℂ) ≠ 0 := by exact_mod_cast left_ne_zero_of_mul hn
    have h2 : (x.2 : ℂ) ≠ 0 := by exact_mod_cast right_ne_zero_of_mul hn
    simp only [twistedVonMangoldtDiv, charDivArith, coe_mk, Nat.cast_mul, map_mul]
    field_simp
  rw [sum_congr rfl h, ← mul_sum,
    Nat.sum_divisorsAntidiagonal (f := fun a _ ↦ (Λ a : ℂ)), ← Complex.ofReal_sum,
    vonMangoldt_sum]
  ring

/-- `T(x) = Σ_{d ≤ x} χ(d) Λ(d)/d · Σ_{m ≤ x/d} χ(m)/m`. -/
theorem logSum_eq_sum (χ : DirichletCharacter ℂ q) (x : ℝ) :
    logSum χ x = ∑ d ∈ Ioc 0 ⌊x⌋₊, χ d * Λ d / d * recipSum χ (x / d) := by
  have h := sum_Ioc_mul_eq_sum_sum (twistedVonMangoldtDiv χ) (charDivArith χ) ⌊x⌋₊
  simp_rw [twistedVonMangoldtDiv_mul_charDiv] at h
  rw [logSum, h]
  refine sum_congr rfl fun d _ ↦ ?_
  rw [recipSum, Nat.floor_div_natCast]
  rfl

/-- **Plan step 4.2**, conditional on the partial-sum estimate
`‖Σ_{m ≤ y} χ(m)/m − L(1, χ)‖ ≤ 2q/y` (`y ≥ 1`):
`‖L(1, χ)‖ · ‖S_χ(x)‖ ≤ ‖T(x)‖ + 2q ψ(x)/x` for `x ≥ 1`. -/
theorem norm_LFunction_one_mul_norm_twistedSum_le_of [NeZero q] (χ : DirichletCharacter ℂ q)
    (hP : ∀ y : ℝ, 1 ≤ y → ‖recipSum χ y - DirichletCharacter.LFunction χ 1‖ ≤ 2 * q / y)
    {x : ℝ} (hx : 1 ≤ x) :
    ‖DirichletCharacter.LFunction χ 1‖ * ‖twistedSum χ x‖ ≤
      ‖logSum χ x‖ + 2 * q * ψ x / x := by
  set L := DirichletCharacter.LFunction χ 1
  have hx0 : 0 < x := by linarith
  have hid : L * twistedSum χ x = logSum χ x +
      ∑ d ∈ Ioc 0 ⌊x⌋₊, χ d * Λ d / d * (L - recipSum χ (x / d)) := by
    rw [logSum_eq_sum, ← sum_add_distrib, twistedSum, mul_sum]
    refine sum_congr rfl fun d _ ↦ ?_
    ring
  have hbound : ‖∑ d ∈ Ioc 0 ⌊x⌋₊, χ d * Λ d / d * (L - recipSum χ (x / d))‖ ≤
      2 * q * ψ x / x := by
    calc _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, ‖χ d * Λ d / d * (L - recipSum χ (x / d))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, 2 * q / x * Λ d := by
          refine sum_le_sum fun d hd ↦ ?_
          rw [mem_Ioc] at hd
          have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
          have hdx : (d : ℝ) ≤ x := (Nat.cast_le.mpr hd.2).trans (Nat.floor_le hx0.le)
          have h1 : 1 ≤ x / d := by rw [le_div_iff₀ hd0]; linarith
          have hP' := hP (x / d) h1
          rw [norm_sub_rev] at hP'
          have hχ := DirichletCharacter.norm_le_one χ d
          have hΛ := (vonMangoldt_nonneg (n := d))
          rw [norm_mul, norm_div, norm_mul, Complex.norm_real, Complex.norm_natCast,
            Real.norm_of_nonneg hΛ]
          calc ‖χ d‖ * Λ d / d * ‖L - recipSum χ (x / d)‖ ≤ 1 * Λ d / d * (2 * q / (x / d)) := by
                gcongr
            _ = 2 * q / x * Λ d := by field_simp
      _ = 2 * q * ψ x / x := by
          rw [← mul_sum, Chebyshev.psi]; ring
  calc ‖L‖ * ‖twistedSum χ x‖ = ‖L * twistedSum χ x‖ := (norm_mul _ _).symm
    _ ≤ ‖logSum χ x‖ + _ := by rw [hid]; exact norm_add_le_of_le le_rfl hbound

end ZInQ.Progressions
