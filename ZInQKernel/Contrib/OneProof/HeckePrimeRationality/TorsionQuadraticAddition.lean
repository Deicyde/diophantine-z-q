import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.TorsionWeierstrassData
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelThetaAddition

/-!
# Quadratic addition for the actual torsion values

The completed-theta addition identity is bound to the actual scaled torsion
values and Mathlib's Weierstrass function. All three torsion labels must be
admissible. The resulting quadratic relation is not a proof that its defect
belongs to an Eisenstein space, nor a trace-closure or spanning theorem.
-/

noncomputable section
set_option autoImplicit false

open Complex UpperHalfPlane

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionQuadraticAddition

open TorsionWeierstrassData CompletedTheta

variable {N : ℕ} [NeZero N]

lemma addition_constant_eq_finitePart (τ : ℍ) :
    ThetaAddition.c τ = ThetaWeierstrass.finitePart τ := rfl

lemma torsionPoint_add (N : ℕ) (a b c d : ℤ) (τ : ℍ) :
    torsionPoint N (a + c) (b + d) τ = torsionPoint N a b τ + torsionPoint N c d τ := by
  unfold torsionPoint
  push_cast
  ring

/-- The scaled value is the negative completed logarithmic derivative. -/
lemma lambdaValue_eq_neg_logDerivative (a b : ℤ) (τ : ℍ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    lambdaValue N a b τ = -ThetaAddition.L τ (torsionPoint N a b τ) -
      (2 * (Real.pi : ℂ) * Complex.I) * (a : ℂ) / (N : ℂ) := by
  rw [lambdaValue_of_good N a b τ hg,
    torsionLogDerivative_eq_deriv N (NeZero.pos N) τ a b hg]
  have hθ := H_torsion_ne_zero N (NeZero.pos N) τ a b hg
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  dsimp [scale, ThetaAddition.L]
  field_simp
  ring

/-- The completion terms cancel for the sum of the two labels. -/
lemma lambdaValue_add_difference (a b c d : ℤ) (τ : ℍ)
    (hp : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b))
    (hq : ¬ ((N : ℤ) ∣ c ∧ (N : ℤ) ∣ d))
    (hs : ¬ ((N : ℤ) ∣ a + c ∧ (N : ℤ) ∣ b + d)) :
    lambdaValue N a b τ + lambdaValue N c d τ - lambdaValue N (a + c) (b + d) τ =
      -(ThetaAddition.L τ (torsionPoint N a b τ) +
        ThetaAddition.L τ (torsionPoint N c d τ) -
        ThetaAddition.L τ (torsionPoint N (a + c) (b + d) τ)) := by
  rw [lambdaValue_eq_neg_logDerivative a b τ hp,
    lambdaValue_eq_neg_logDerivative c d τ hq,
    lambdaValue_eq_neg_logDerivative (a + c) (b + d) τ hs]
  push_cast
  ring

/-- Actual torsion Frobenius–Stickelberger addition on its nonzero-label domain. -/
theorem lambdaValue_frobenius_stickelberger (a b c d : ℤ) (τ : ℍ)
    (hp : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b))
    (hq : ¬ ((N : ℤ) ∣ c ∧ (N : ℤ) ∣ d))
    (hs : ¬ ((N : ℤ) ∣ a + c ∧ (N : ℤ) ∣ b + d)) :
    (lambdaValue N a b τ + lambdaValue N c d τ - lambdaValue N (a + c) (b + d) τ) ^ 2 =
      xValue N a b τ + xValue N c d τ + xValue N (a + c) (b + d) τ := by
  have hP := H_torsion_ne_zero N (NeZero.pos N) τ a b hp
  have hQ := H_torsion_ne_zero N (NeZero.pos N) τ c d hq
  have hS := H_torsion_ne_zero N (NeZero.pos N) τ (a + c) (b + d) hs
  have hPQ : H τ (torsionPoint N a b τ + torsionPoint N c d τ) ≠ 0 := by
    rw [← torsionPoint_add]
    exact hS
  have hFS := ThetaAddition.frobenius_stickelberger τ
    (torsionPoint N a b τ) (torsionPoint N c d τ) hP hQ hPQ
  have hWP (x : ℂ) (hx : H τ x ≠ 0) :
      (ThetaWeierstrass.periodPair τ).weierstrassP x =
        -deriv (ThetaAddition.L τ) x + ThetaAddition.c τ := by
    rw [addition_constant_eq_finitePart]
    exact ThetaWeierstrass.weierstrassP_eq_neg_deriv_logDerivative τ x
      (fun h => hx ((ThetaWeierstrass.H_zero_iff_mem_lattice τ x).mpr h))
  rw [lambdaValue_add_difference a b c d τ hp hq hs, neg_sq,
    xValue_of_good N a b τ hp, xValue_of_good N c d τ hq,
    xValue_of_good N (a + c) (b + d) τ hs, torsionPoint_add,
    hWP _ hP, hWP _ hQ, hWP _ hPQ]
  linear_combination hFS

/-- The exact quadratic defect equals a sum of the actual quadratic values.
Their Eisenstein membership is a separate, unproved obligation. -/
theorem quadratic_addition (a b c d : ℤ) (τ : ℍ)
    (hp : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b))
    (hq : ¬ ((N : ℤ) ∣ c ∧ (N : ℤ) ∣ d))
    (hs : ¬ ((N : ℤ) ∣ a + c ∧ (N : ℤ) ∣ b + d)) :
    lambdaValue N a b τ * lambdaValue N c d τ -
      lambdaValue N a b τ * lambdaValue N (a + c) (b + d) τ -
      lambdaValue N c d τ * lambdaValue N (a + c) (b + d) τ =
        -muValue N a b τ - muValue N c d τ - muValue N (a + c) (b + d) τ := by
  have hFS := lambdaValue_frobenius_stickelberger a b c d τ hp hq hs
  unfold muValue
  linear_combination hFS / 2

end ZInQ.Contrib.HeckePrimeRationality.TorsionQuadraticAddition
