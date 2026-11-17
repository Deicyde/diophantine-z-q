import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.TorsionQuadraticAddition
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionFourierComparison

/-!
# All label cases of the actual torsion quadratic defect

The nondegenerate addition formula and the explicit zero convention give
an exact formula for every pair of integer torsion labels. At a zero class
the defect is a negative square, not the nondegenerate three-mu formula.
The square is expressed through the actual Weierstrass and quadratic values.
No Eisenstein membership or trace closure is asserted.
-/

noncomputable section
set_option autoImplicit false

open Complex UpperHalfPlane

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionQuadraticCases

open TorsionWeierstrassData

variable {N : ℕ} [NeZero N]

/-- The actual quadratic defect on two torsion labels. -/
def quadraticDefect (N : ℕ) (a b c d : ℤ) (τ : ℍ) : ℂ :=
  lambdaValue N a b τ * lambdaValue N c d τ -
    lambdaValue N a b τ * lambdaValue N (a + c) (b + d) τ -
    lambdaValue N c d τ * lambdaValue N (a + c) (b + d) τ

lemma lambdaValue_of_bad (a b : ℤ) (τ : ℍ)
    (hp : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b) : lambdaValue N a b τ = 0 := by
  rw [lambdaValue, TorsionDistributionTwo.reg_of_bad hp, mul_zero]

/-- This equality uses the definition of the actual quadratic value; it is
not an Eisenstein identification. -/
lemma lambdaValue_square (a b : ℤ) (τ : ℍ) :
    lambdaValue N a b τ ^ 2 = xValue N a b τ + 2 * muValue N a b τ := by
  unfold muValue
  ring

lemma lambdaValue_eq_neg_of_sum_bad (a b c d : ℤ) (τ : ℍ)
    (hs : (N : ℤ) ∣ a + c ∧ (N : ℤ) ∣ b + d) :
    lambdaValue N c d τ = -lambdaValue N a b τ := by
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := hs
  have hc : c = -a + (N : ℤ) * m := by linear_combination hm
  have hd : d = -b + (N : ℤ) * n := by linear_combination hn
  rw [lambdaValue, hc, hd, TorsionFourierComparison.reg_shift,
    TorsionFourierComparison.reg_neg, lambdaValue]
  ring

lemma defect_of_bad_left (a b c d : ℤ) (τ : ℍ)
    (hp : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b) :
    quadraticDefect N a b c d τ = -(xValue N c d τ + 2 * muValue N c d τ) := by
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := hp
  have ha : a = (N : ℤ) * m := hm
  have hb : b = (N : ℤ) * n := hn
  have hS : lambdaValue N (a + c) (b + d) τ = lambdaValue N c d τ := by
    rw [lambdaValue, ha, hb]
    rw [show (N : ℤ) * m + c = c + (N : ℤ) * m by ring,
      show (N : ℤ) * n + d = d + (N : ℤ) * n by ring,
      TorsionFourierComparison.reg_shift]
    rfl
  rw [quadraticDefect, lambdaValue_of_bad a b τ ⟨⟨m, hm⟩, ⟨n, hn⟩⟩, hS]
  have hsq := lambdaValue_square (N := N) c d τ
  linear_combination -hsq

lemma defect_of_bad_right (a b c d : ℤ) (τ : ℍ)
    (hq : (N : ℤ) ∣ c ∧ (N : ℤ) ∣ d) :
    quadraticDefect N a b c d τ = -(xValue N a b τ + 2 * muValue N a b τ) := by
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := hq
  have hS : lambdaValue N (a + c) (b + d) τ = lambdaValue N a b τ := by
    rw [lambdaValue, hm, hn, TorsionFourierComparison.reg_shift]
    rfl
  rw [quadraticDefect, lambdaValue_of_bad c d τ ⟨⟨m, hm⟩, ⟨n, hn⟩⟩, hS]
  have hsq := lambdaValue_square (N := N) a b τ
  linear_combination -hsq

lemma defect_of_bad_sum (a b c d : ℤ) (τ : ℍ)
    (hs : (N : ℤ) ∣ a + c ∧ (N : ℤ) ∣ b + d) :
    quadraticDefect N a b c d τ = -(xValue N a b τ + 2 * muValue N a b τ) := by
  rw [quadraticDefect, lambdaValue_of_bad (a + c) (b + d) τ hs,
    lambdaValue_eq_neg_of_sum_bad a b c d τ hs]
  have hsq := lambdaValue_square (N := N) a b τ
  linear_combination -hsq

/-- All label cases, with the exceptional negative-square terms retained. -/
theorem quadraticDefect_cases (a b c d : ℤ) (τ : ℍ) :
    quadraticDefect N a b c d τ =
      if (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b then
        -(xValue N c d τ + 2 * muValue N c d τ)
      else if (N : ℤ) ∣ c ∧ (N : ℤ) ∣ d then
        -(xValue N a b τ + 2 * muValue N a b τ)
      else if (N : ℤ) ∣ a + c ∧ (N : ℤ) ∣ b + d then
        -(xValue N a b τ + 2 * muValue N a b τ)
      else -muValue N a b τ - muValue N c d τ - muValue N (a + c) (b + d) τ := by
  classical
  by_cases hp : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b
  · rw [if_pos hp]
    exact defect_of_bad_left a b c d τ hp
  · rw [if_neg hp]
    by_cases hq : (N : ℤ) ∣ c ∧ (N : ℤ) ∣ d
    · rw [if_pos hq]
      exact defect_of_bad_right a b c d τ hq
    · rw [if_neg hq]
      by_cases hs : (N : ℤ) ∣ a + c ∧ (N : ℤ) ∣ b + d
      · rw [if_pos hs]
        exact defect_of_bad_sum a b c d τ hs
      · rw [if_neg hs]
        exact TorsionQuadraticAddition.quadratic_addition a b c d τ hp hq hs

end ZInQ.Contrib.HeckePrimeRationality.TorsionQuadraticCases
