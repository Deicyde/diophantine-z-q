import ZInQKernel.Contrib.OneProof.RC.ModelTarget.ChartSmooth

/-! Smoothness of the `Y`-chart of the projective Weierstrass cubic, given a shear
constant `c` with `c³ + a₂c² + a₄c + a₆` a unit (inverse `-w`). The sheared
presentation is standard étale over the polynomial ring in `x'` after inverting its
derivative; the derivative and `z = Z/Y` generate the unit ideal (at a point with
`z = 0` the equation forces `x' = 0`, where the derivative is the unit `w`); and
inverting `z` gives the overlap `D₊(YZ)`, a localization of the smooth `Z`-chart.
On the spot (c). -/

noncomputable section

open WeierstrassCurve HomogeneousLocalization
open Polynomial (C derivative)

set_option autoImplicit false

namespace ZInQ.Manuscript.RC.ModelTarget

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) {c w : R}

/-- The derivative of the sheared presentation in `z`. -/
def yDeriv (c w : R) : Polynomial (Polynomial R) :=
  3 * Polynomial.X ^ 2 +
    2 * C (C w * (C (W.a₁ * c + W.a₃) - C (3 * c ^ 2 + 2 * W.a₂ * c + W.a₄) * Polynomial.X)) *
      Polynomial.X +
    C (C w * (1 + C W.a₁ * Polynomial.X - C (3 * c + W.a₂) * Polynomial.X ^ 2))

omit [CommRing R] in
theorem derivative_yPoly {R : Type} [CommRing R] (W : WeierstrassCurve R) (c w : R) :
    derivative (yPoly W c w) = yDeriv W c w := by
  have hC : ∀ (p : Polynomial R) (n : ℕ), derivative (C p ^ n) = 0 := fun p n => by
    rw [← Polynomial.C_pow, Polynomial.derivative_C]
  simp [yPoly, yDeriv, map_ofNat, hC] <;> ring

omit [CommRing R] in
theorem yPoly_monic {R : Type} [CommRing R] (W : WeierstrassCurve R) (c w : R) :
    (yPoly W c w).Monic := by
  unfold yPoly
  monicity!

theorem smooth_ydz (hw : w * (c ^ 3 + W.a₂ * c ^ 2 + W.a₄ * c + W.a₆) = -1) :
    RingHom.Smooth ((algebraMap (Chart W 1)
      (Localization.Away (yEquiv W hw (AdjoinRoot.mk _ (yDeriv W c w))))).comp
        (chartConst W 1)) := by
  have h := smooth_away_derivative (yPoly W c w) (yPoly_monic W c w)
  rw [derivative_yPoly] at h
  exact smooth_transport (chartConst W 1) (yEquiv W hw)
    (fun a => by exact presEquiv_algebraMap _ _ _ _ _ _ _ _ _ _ _ _ a) _ h

/-- On the `Y`-chart the sheared derivative and `z` generate the unit ideal. -/
theorem span_yChart (hw : w * (c ^ 3 + W.a₂ * c ^ 2 + W.a₄ * c + W.a₆) = -1) :
    Ideal.span {yEquiv W hw (AdjoinRoot.mk _ (yDeriv W c w)), ratio W 1 2} = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  let _ := Ideal.Quotient.field m
  let π := Ideal.Quotient.mk m
  have hzero (b : Chart W 1)
      (hb : b ∈ Ideal.span {yEquiv W hw (AdjoinRoot.mk _ (yDeriv W c w)), ratio W 1 2}) :
      π b = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle hb)
  have hD := hzero _ (Ideal.subset_span (Set.mem_insert _ _))
  have hz : π (ratio W 1 2) = 0 := hzero _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  have hx : π (ratio W 1 0) = 0 := by
    have h := congrArg π (chart_equation W 1)
    rw [map_zero, ← MvPolynomial.coe_eval₂Hom, ← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom,
      MvPolynomial.coe_eval₂Hom] at h
    simp only [Projective.polynomial, MvPolynomial.eval₂_add, MvPolynomial.eval₂_sub,
      MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X, MvPolynomial.eval₂_C,
      RingHom.comp_apply, ratio_self, map_one, hz] at h
    have h3 : π (ratio W 1 0) ^ 3 = 0 := by linear_combination -h
    exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h3
  have e1 : yEquiv W hw (AdjoinRoot.mk _ (yDeriv W c w)) = presLift W 1 (yPoly W c w)
      (ratio W 1 0 - chartConst W 1 c * ratio W 1 2) (ratio W 1 2) (y_eval W hw)
      (AdjoinRoot.mk _ (yDeriv W c w)) := rfl
  rw [e1, presLift, AdjoinRoot.lift_mk] at hD
  simp only [yDeriv, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_ofNat, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_sub, Polynomial.eval₂_one, map_add, map_mul, map_pow, map_sub, map_ofNat,
    map_one, hx, hz] at hD
  have hw0 : π (chartConst W 1 w) = 0 := by linear_combination hD
  have hw' := congrArg (π.comp (chartConst W 1)) hw
  simp only [RingHom.comp_apply, map_mul, map_neg, map_one, hw0, zero_mul] at hw'
  exact one_ne_zero (neg_eq_zero.mp hw'.symm)

private theorem coord_mem (j : Fin 3) : W.toProjective.coord j ∈ W.toProjective.grading 1 :=
  W.toProjective.coord_mem_grading j

/-- Away from `z`, the `Y`-chart is the overlap `D₊(YZ)`, a localization of the
`Z`-chart; so it is smooth. -/
theorem smooth_yChart_awayZ [W.IsElliptic] :
    RingHom.Smooth ((algebraMap (Chart W 1) (Localization.Away (ratio W 1 2))).comp
      (chartConst W 1)) := by
  let m₁ := awayMap W.toProjective.grading (coord_mem W 2) (rfl : W.toProjective.coord 1 * W.toProjective.coord 2 = W.toProjective.coord 1 * W.toProjective.coord 2)
  let m₂ := awayMap W.toProjective.grading (coord_mem W 1) (mul_comm _ _ : W.toProjective.coord 1 * W.toProjective.coord 2 = W.toProjective.coord 2 * W.toProjective.coord 1)
  have hsame : m₁.comp (chartConst W 1) = m₂.comp (chartConst W 2) := by
    refine RingHom.ext fun r => ?_
    simp only [RingHom.comp_apply, chartConst, m₁, m₂, awayMap_fromZeroRingHom]
  have h₂ : RingHom.Smooth (m₂.comp (chartConst W 2)) := by
    let _ := m₂.toAlgebra
    have := Away.isLocalization_mul (coord_mem W 2) (coord_mem W 1)
      (mul_comm _ _ : W.toProjective.coord 1 * W.toProjective.coord 2 = W.toProjective.coord 2 * W.toProjective.coord 1) one_ne_zero
    exact (smooth_chartZ W).comp (RingHom.Smooth.holdsForLocalizationAway
      (Away W.toProjective.grading (W.toProjective.coord 1 * W.toProjective.coord 2))
      (Away.isLocalizationElem (coord_mem W 2) (coord_mem W 1)))
  let _ := m₁.toAlgebra
  have hloc : IsLocalization.Away (ratio W 1 2) (Away W.toProjective.grading (W.toProjective.coord 1 * W.toProjective.coord 2)) := by
    have := Away.isLocalization_mul (coord_mem W 1) (coord_mem W 2)
      (rfl : W.toProjective.coord 1 * W.toProjective.coord 2 = W.toProjective.coord 1 * W.toProjective.coord 2) one_ne_zero
    have helem : Away.isLocalizationElem (coord_mem W 1) (coord_mem W 2) = ratio W 1 2 := by
      apply HomogeneousLocalization.val_injective
      simp [ratio, Away.val_mk]
    rwa [helem] at this
  let ε := IsLocalization.algEquiv (Submonoid.powers (ratio W 1 2))
    (Localization.Away (ratio W 1 2)) (Away W.toProjective.grading (W.toProjective.coord 1 * W.toProjective.coord 2))
  have hε : (algebraMap (Chart W 1) (Localization.Away (ratio W 1 2))).comp (chartConst W 1) =
      (ε.symm : Away W.toProjective.grading (W.toProjective.coord 1 * W.toProjective.coord 2) →+* Localization.Away (ratio W 1 2)).comp (m₁.comp (chartConst W 1)) := by
    refine RingHom.ext fun r => ?_
    change _ = ε.symm (algebraMap (Chart W 1) (Away W.toProjective.grading (W.toProjective.coord 1 * W.toProjective.coord 2)) (chartConst W 1 r))
    rw [AlgEquiv.commutes]
    rfl
  rw [hε, hsame]
  exact h₂.comp (RingHom.Smooth.of_bijective ε.symm.bijective)

/-- The `Y`-chart of the projective cubic is smooth over the base. -/
theorem smooth_chartY [W.IsElliptic] (hw : w * (c ^ 3 + W.a₂ * c ^ 2 + W.a₄ * c + W.a₆) = -1) :
    RingHom.Smooth (chartConst W 1) := by
  refine RingHom.Smooth.ofLocalizationSpanTarget (chartConst W 1) _ (span_yChart W hw) ?_
  rintro ⟨r, hr⟩
  rcases hr with rfl | rfl
  · exact smooth_ydz W hw
  · exact smooth_yChart_awayZ W

#print axioms smooth_ydz
#print axioms span_yChart
#print axioms smooth_yChart_awayZ
#print axioms smooth_chartY

end ZInQ.Manuscript.RC.ModelTarget
