import ZInQKernel.OneProof.H.TailY

/-! # Exact Bost normalization and two proof boundaries

This file does not prove `ZInQ.HeightSplit.BostLowerBound` and introduces no
published-theorem assumption.  The scalar counterexample concerns only reversing
the coarser numerical bound; it is not a counterexample abelian variety.
The coefficient lemma fixes the same uniformization and does not forbid a
legitimate simultaneous change of coordinates and periods.
-/

namespace ZInQ.Contrib.CloudB3SC4Bost

open ZInQ.DefFaltings ZInQ.HeightSplit

/-- The exact Deligne-to-original-Faltings logarithmic constant. -/
theorem log_two_pi_sq :
    Real.log (2 * Real.pi) + Real.log Real.pi = Real.log (2 * Real.pi ^ 2) := by
  rw [← Real.log_mul (by positivity) Real.pi_pos.ne']
  congr 1
  ring

/-- The exact Bost scalar conclusion in the kernel's original normalization. -/
theorem exact_bost_bound_iff (g : ℕ) (x : ℝ) :
    (-((g : ℝ) / 2 * Real.log (2 * Real.pi)) ≤
      x + (g : ℝ) / 2 * Real.log Real.pi) ↔
    -((g : ℝ) / 2 * Real.log (2 * Real.pi ^ 2)) ≤ x := by
  rw [← log_two_pi_sq]
  constructor <;> intro h <;> nlinarith

/-- The coarser R21 constant is strictly below the exact Bost threshold at g=1. -/
theorem coarse_constant_gap_pos :
    0 < (3 / 2 : ℝ) - (1 / 2) * Real.log (2 * Real.pi ^ 2) := by
  rw [← log_two_pi_sq]
  have h := ZInQ.HeightSplit.log_two_pi_add_log_pi_lt_three
  linarith

/-- Numerical R21 does not, by itself, imply the exact scalar Bost conclusion. -/
theorem coarse_scalar_bound_not_bost :
    ∃ (g : ℕ) (x : ℝ), -(3 / 2) * (g : ℝ) ≤ x ∧
      ¬ (-((g : ℝ) / 2 * Real.log (2 * Real.pi)) ≤
        x + (g : ℝ) / 2 * Real.log Real.pi) := by
  refine ⟨1, -(3 / 2), by norm_num, ?_⟩
  intro h
  norm_num only [Nat.cast_one] at h
  have hlog := ZInQ.HeightSplit.log_two_pi_add_log_pi_lt_three
  linarith

section CoefficientPin

variable {K : Type} [Field K] {A : PkgI3.AbVar K}
  {L : Type} [Field L] [NumberField L] [Algebra K L] {g : ℕ}

/-- Keeping the same `Φ` and both Jacobian coefficient pins rules out a nontrivial
rescaling of a genuine metrized-model coefficient. -/
theorem coefficient_rescale_eq_one_of_fixed_uniformization
    (M : MetrizedModel A L g) (τ : L →+* ℂ)
    (Φ : (Fin g → ℂ) → M.model.Pts τ)
    (hcoeff : ∀ f : Fin g → IsLocalRing.maximalIdeal M.model.genStalk,
      M.hodge.coeff τ (M.model.wedge f) = M.model.jacDet Φ f)
    (q : ℂ)
    (hq : ∀ f : Fin g → IsLocalRing.maximalIdeal M.model.genStalk,
      (q • M.hodge.coeff τ) (M.model.wedge f) = M.model.jacDet Φ f) :
    q = 1 := by
  have heq : q • M.hodge.coeff τ = M.hodge.coeff τ := by
    apply GroupModel.semilinear_ext_wedge M.model
    intro f
    exact (hq f).trans (hcoeff f).symm
  obtain ⟨v, _, hv, _⟩ := M.hodge.isLattice
  apply mul_right_cancel₀ (M.hodge.coeff_apply_ne_zero τ hv)
  have hval := congrArg
    (fun c : M.model.hodgeSpace g →ₛₗ[τ] ℂ => c v) heq
  simpa only [LinearMap.smul_apply, smul_eq_mul, one_mul] using hval

end CoefficientPin

end ZInQ.Contrib.CloudB3SC4Bost
