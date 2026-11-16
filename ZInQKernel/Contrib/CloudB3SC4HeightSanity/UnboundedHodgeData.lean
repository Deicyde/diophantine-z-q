import ZInQKernel.HDecomp.Faltings.HodgeData

/-!
# Arbitrary Hodge data have no uniform lower height bound

This checks an important boundary of the existing definitions. The coefficient
map of raw `HodgeData` may be rescaled, so its real-valued `modelHeight` can be
any real number. This is not a counterexample to `BostLowerBound`: an actual
`MetrizedModel` additionally pins the coefficient map to the Jacobian of its
analytic uniformization. Those compatibility conditions are not assumed here.
-/

noncomputable section

namespace ZInQ.Contrib.HeightSanity

open NumberField ZInQ.DefFaltings

/-- Rescale the coefficient map of the existing rational example, keeping
its integral lattice and period lattice fixed. -/
noncomputable def scaledExampleHodge (c : ℝ) (hc : 0 < c) : HodgeData ℚ 1 ℚ where
  lattice := exampleHodge.lattice
  finrank_eq_one := exampleHodge.finrank_eq_one
  isLattice := exampleHodge.isLattice
  periods := exampleHodge.periods
  periods_discrete := exampleHodge.periods_discrete
  periods_isZLattice := exampleHodge.periods_isZLattice
  coeff σ := (c : ℂ) • exampleHodge.coeff σ
  coeff_ne_zero σ := smul_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne')
    (exampleHodge.coeff_ne_zero σ)

/-- The fixed-period coefficient rescaling subtracts `log c` from the height. -/
theorem scaledExampleHodge_height (c : ℝ) (hc : 0 < c) :
    (scaledExampleHodge c hc).modelHeight = exampleHodge.modelHeight - Real.log c := by
  have hu : (Finset.univ : Finset (ℚ →+* ℂ)) = {Rat.castHom ℂ} := by
    ext σ
    simp [Subsingleton.elim σ (Rat.castHom ℂ)]
  have hm : torusMetricSq ((scaledExampleHodge c hc).periods (Rat.castHom ℂ))
      ((scaledExampleHodge c hc).coeff (Rat.castHom ℂ) 1) =
      c ^ 2 * ZLattice.covolume gaussianPair.lattice := by
    simp [scaledExampleHodge, exampleHodge, ratCoeff, torusMetricSq,
      LinearMap.smul_apply, Complex.norm_real, abs_of_pos hc,
      PeriodPair.covolume_lattice1]
  have hv : 0 < ZLattice.covolume gaussianPair.lattice :=
    ZLattice.covolume_pos gaussianPair.lattice MeasureTheory.volume
  rw [HodgeData.modelHeight_of_span (scaledExampleHodge c hc) (η₀ := (1 : ℚ)) rfl
      one_ne_zero, hu, Finset.sum_singleton, hm, Module.finrank_self,
      Nat.cast_one, div_one, exampleHodge_modelHeight]
  rw [Real.log_mul (pow_ne_zero 2 hc.ne') hv.ne', Real.log_pow]
  ring

/-- Every real number is the height of raw Hodge data with the existing
rational integral and period lattices. -/
theorem exists_hodgeData_with_height (x : ℝ) :
    ∃ D : HodgeData ℚ 1 ℚ, D.modelHeight = x := by
  refine ⟨scaledExampleHodge (Real.exp (exampleHodge.modelHeight - x)) (Real.exp_pos _), ?_⟩
  rw [scaledExampleHodge_height, Real.log_exp]
  ring

/-- In particular, raw Hodge data alone have no real lower height bound. -/
theorem exists_hodgeData_below (b : ℝ) :
    ∃ D : HodgeData ℚ 1 ℚ, D.modelHeight < b := by
  obtain ⟨D, hD⟩ := exists_hodgeData_with_height (b - 1)
  refine ⟨D, ?_⟩
  rw [hD]
  linarith

/-- Applying Bost's numerical bound to all raw Hodge data would be false.
This does not assert anything false about the actual abelian-variety target. -/
theorem not_bost_bound_for_raw_hodgeData :
    ¬ ∀ D : HodgeData ℚ 1 ℚ,
      -((1 : ℝ) / 2 * Real.log (2 * Real.pi)) ≤
        D.modelHeight + (1 : ℝ) / 2 * Real.log Real.pi := by
  intro h
  obtain ⟨D, hD⟩ := exists_hodgeData_with_height
    (-((1 : ℝ) / 2 * Real.log (2 * Real.pi)) - (1 : ℝ) / 2 * Real.log Real.pi - 1)
  have hh := h D
  rw [hD] at hh
  linarith

end ZInQ.Contrib.HeightSanity
