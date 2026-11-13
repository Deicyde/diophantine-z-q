import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Formal Euler coefficients and Hasse roots

All coefficient statements concern the inverse of the formal Euler polynomial,
not an analytic or numerically computed reciprocal. Repeated roots are allowed.
-/

namespace ZInQ.Contrib.Hasse

open PowerSeries

/-- Hasse's real inequality constructs two complex roots with the correct norm. -/
theorem exists_hasse_roots {a p : ℝ} (hp : 0 ≤ p) (ha : |a| ≤ 2 * Real.sqrt p) :
    ∃ α β : ℂ, α + β = (a : ℂ) ∧ α * β = (p : ℂ) ∧
      ‖α‖ = Real.sqrt p ∧ ‖β‖ = Real.sqrt p := by
  have hasq : a ^ 2 ≤ 4 * p := by
    nlinarith [sq_abs a, Real.sq_sqrt hp, Real.sqrt_nonneg p, abs_nonneg a]
  let t : ℝ := Real.sqrt (4 * p - a ^ 2)
  have ht : t ^ 2 = 4 * p - a ^ 2 := Real.sq_sqrt (by linarith)
  let α : ℂ := (a : ℂ) / 2 + (t : ℂ) / 2 * Complex.I
  let β : ℂ := (a : ℂ) / 2 - (t : ℂ) / 2 * Complex.I
  have hα : ‖α‖ ^ 2 = p := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [α, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.div_ofNat, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    nlinarith
  have hβ : ‖β‖ ^ 2 = p := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [β, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.div_ofNat, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    nlinarith
  refine ⟨α, β, by dsimp [α, β]; ring, ?_, ?_, ?_⟩
  · apply Complex.ext
    · simp only [α, β, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.sub_re,
        Complex.add_im, Complex.sub_im, Complex.div_ofNat, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      nlinarith
    · simp [α, β, Complex.mul_im, Complex.mul_re, Complex.div_ofNat]
      ring
  · nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg p, norm_nonneg α]
  · nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg p, norm_nonneg β]

/-- The geometric series is a formal multiplicative inverse, even when `α = 0`. -/
theorem geometric_mul (α : ℂ) :
    (1 - C α * X) * (mk fun n => α ^ n) = (1 : PowerSeries ℂ) := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp [sub_mul, mul_assoc, pow_succ']

/-- The inverse's coefficients equal the root-convolution coefficients.
The proof uses formal power-series identities and is valid for repeated roots. -/
theorem coeff_inv_euler_eq (a p : ℤ) (α β : ℂ)
    (hs : α + β = (a : ℂ)) (hp : α * β = (p : ℂ)) (k : ℕ) :
    ((coeff k (invOfUnit
      ((1 - Polynomial.C a * Polynomial.X + Polynomial.C p * Polynomial.X ^ 2 : Polynomial ℤ)
        : PowerSeries ℤ) 1) : ℤ) : ℂ) =
      ∑ ij ∈ Finset.antidiagonal k, α ^ ij.1 * β ^ ij.2 := by
  let P : PowerSeries ℤ :=
    (1 - Polynomial.C a * Polynomial.X + Polynomial.C p * Polynomial.X ^ 2 : Polynomial ℤ)
  let S : PowerSeries ℂ := map (Int.castRingHom ℂ) (invOfUnit P 1)
  let Q : PowerSeries ℂ := 1 - C (a : ℂ) * X + C (p : ℂ) * X ^ 2
  let G : PowerSeries ℂ := (mk fun n => α ^ n) * (mk fun n => β ^ n)
  have hP : constantCoeff P = ((1 : ℤˣ) : ℤ) := by simp [P]
  have hmap : map (Int.castRingHom ℂ) P = Q := by
    dsimp only [P, Q]
    simp only [Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_mul,
      Polynomial.coe_pow, Polynomial.coe_one, Polynomial.coe_C, Polynomial.coe_X,
      map_add, map_sub, map_mul, map_pow, map_one, map_C, map_X]
    rfl
  have hS : Q * S = 1 := by
    dsimp only [S]
    rw [← hmap, ← map_mul, mul_invOfUnit P 1 hP, map_one]
  have hfactor : Q = (1 - C α * X) * (1 - C β * X) := by
    calc
      _ = 1 - C (α + β) * X + C (α * β) * X ^ 2 := by rw [hs, hp]
      _ = _ := by rw [map_add, map_mul]; ring
  have hG : Q * G = 1 := by
    dsimp only [G]
    rw [hfactor]
    calc
      _ = ((1 - C α * X) * (mk fun n => α ^ n)) *
        ((1 - C β * X) * (mk fun n => β ^ n)) := by ring
      _ = 1 := by rw [geometric_mul, geometric_mul, one_mul]
  have heq : S = G := by
    calc
      S = S * (Q * G) := by rw [hG, mul_one]
      _ = (Q * S) * G := by ring
      _ = G := by rw [hS, one_mul]
  have hc := congrArg (coeff k) heq
  simpa [S, P, G, coeff_mul] using hc

/-- The formal good-prime Euler coefficients satisfy the sharp divisor-type majorant. -/
theorem norm_coeff_inv_euler_le (a p : ℤ) (hp : 0 ≤ (p : ℝ))
    (ha : |(a : ℝ)| ≤ 2 * Real.sqrt (p : ℝ)) (k : ℕ) :
    ‖((coeff k (invOfUnit
      ((1 - Polynomial.C a * Polynomial.X + Polynomial.C p * Polynomial.X ^ 2 : Polynomial ℤ)
        : PowerSeries ℤ) 1) : ℤ) : ℂ)‖ ≤ (k + 1) * (Real.sqrt (p : ℝ)) ^ k := by
  obtain ⟨α, β, hs, hprod, hα, hβ⟩ := exists_hasse_roots hp ha
  rw [coeff_inv_euler_eq a p α β (by exact_mod_cast hs) (by exact_mod_cast hprod)]
  calc
    _ ≤ ∑ ij ∈ Finset.antidiagonal k, ‖α ^ ij.1 * β ^ ij.2‖ := norm_sum_le _ _
    _ = ∑ _ij ∈ Finset.antidiagonal k, (Real.sqrt (p : ℝ)) ^ k := by
      apply Finset.sum_congr rfl
      intro ij hij
      rw [norm_mul, norm_pow, norm_pow, hα, hβ, ← pow_add, Finset.mem_antidiagonal.mp hij]
    _ = _ := by simp

/-- The actual formal inverse satisfies the second-order Euler recurrence. -/
theorem coeff_inv_euler_recurrence (a p : ℤ) (k : ℕ) :
    let S := invOfUnit
      ((1 - Polynomial.C a * Polynomial.X + Polynomial.C p * Polynomial.X ^ 2 : Polynomial ℤ)
        : PowerSeries ℤ) 1
    coeff (k + 2) S = a * coeff (k + 1) S - p * coeff k S := by
  let P : PowerSeries ℤ :=
    (1 - Polynomial.C a * Polynomial.X + Polynomial.C p * Polynomial.X ^ 2 : Polynomial ℤ)
  have hP : constantCoeff P = ((1 : ℤˣ) : ℤ) := by simp [P]
  have h := congrArg (coeff (k + 2)) (mul_invOfUnit P 1 hP)
  simp only [P, Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_mul,
    Polynomial.coe_pow, Polynomial.coe_one, Polynomial.coe_C, Polynomial.coe_X,
    add_mul, sub_mul, one_mul, mul_assoc, map_add, map_sub, coeff_C_mul,
    coeff_succ_X_mul, coeff_X_pow_mul, coeff_one, show k + 2 ≠ 0 by omega,
    ↓reduceIte] at h
  dsimp only
  simp only [Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_mul,
    Polynomial.coe_pow, Polynomial.coe_one, Polynomial.coe_C, Polynomial.coe_X]
  linarith

end ZInQ.Contrib.Hasse
