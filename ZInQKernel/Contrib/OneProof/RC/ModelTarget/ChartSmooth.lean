import ZInQKernel.Contrib.OneProof.RC.ModelTarget.ChartPresentation
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.RingHom.Smooth

/-! Smoothness of the charts of the projective Weierstrass cubic over a base ring on
which the discriminant is a unit (the Jacobian criterion, Silverman, *The Arithmetic
of Elliptic Curves*, 2009, VII.5 and Katz–Mazur 1985 §2.2, both UNVERIFIED; used as
background only). Each presentation of `ChartPresentation` is monic in its outer
variable, so its localization at the derivative is standard étale over a polynomial
ring in one variable (`StandardEtalePair`), hence smooth over the base. On the
`Z`-chart the two partial derivatives generate the unit ideal because every point
with values in a field is nonsingular. On the `Y`-chart the sheared derivative and
`z` generate the unit ideal, and away from `z` the chart is a localization of the
`Z`-chart. On the spot (c). -/

noncomputable section

open WeierstrassCurve HomogeneousLocalization
open Polynomial (C derivative)

set_option autoImplicit false

namespace ZInQ.Manuscript.RC.ModelTarget

variable {R : Type} [CommRing R]

/-- A monic polynomial over `R[X]`, localized at its derivative, is smooth over `R`. -/
theorem smooth_away_derivative (q : Polynomial (Polynomial R)) (hq : q.Monic) :
    RingHom.Smooth ((algebraMap (AdjoinRoot q)
      (Localization.Away (AdjoinRoot.mk q (derivative q)))).comp (algebraMap R (AdjoinRoot q))) := by
  let P : StandardEtalePair (Polynomial R) :=
    ⟨q, hq, derivative q, ⟨1, 0, 1, by ring⟩⟩
  have hS : Algebra.Smooth (Polynomial R) (Localization.Away (AdjoinRoot.mk q (derivative q))) :=
    Algebra.Smooth.of_equiv P.equivAwayAdjoinRoot
  have : Algebra.Smooth R (Polynomial R) := {}
  have h₁ : RingHom.Smooth (algebraMap R (Polynomial R)) := RingHom.smooth_algebraMap.mpr inferInstance
  have h₂ : RingHom.Smooth (algebraMap (Polynomial R)
      (Localization.Away (AdjoinRoot.mk q (derivative q)))) := RingHom.smooth_algebraMap.mpr hS
  have h := h₁.comp h₂
  convert h using 1
  ext r
  simp [IsScalarTower.algebraMap_apply R (Polynomial R) (AdjoinRoot q),
    IsScalarTower.algebraMap_apply (Polynomial R) (AdjoinRoot q)
      (Localization.Away (AdjoinRoot.mk q (derivative q)))]

/-- Transport smoothness of a localization along a ring isomorphism. -/
theorem smooth_transport {B C : Type} [CommRing B] [CommRing C] [Algebra R B]
    (f : R →+* C) (e : B ≃+* C) (he : ∀ r, e (algebraMap R B r) = f r) (s : B)
    (h : RingHom.Smooth ((algebraMap B (Localization.Away s)).comp (algebraMap R B))) :
    RingHom.Smooth ((algebraMap C (Localization.Away (e s))).comp f) := by
  let ε : Localization.Away s ≃+* Localization.Away (e s) :=
    IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers s) (T := Submonoid.powers (e s))
      _ _ e (by rw [Submonoid.map_powers]; rfl)
  have hε := h.comp (RingHom.Smooth.of_bijective ε.bijective)
  convert hε using 1
  ext r
  simp only [RingHom.comp_apply]
  rw [IsLocalization.map_eq, RingHom.coe_coe, he]

variable (W : WeierstrassCurve R)

theorem derivative_affinePolynomial : derivative W.toAffine.polynomial = W.toAffine.polynomialY := by
  have h3 : derivative (C (Polynomial.X : Polynomial R) ^ 3) = 0 := by
    rw [← Polynomial.C_pow, Polynomial.derivative_C]
  have h2 : derivative (C (Polynomial.X : Polynomial R) ^ 2) = 0 := by
    rw [← Polynomial.C_pow, Polynomial.derivative_C]
  simp [Affine.polynomial, Affine.polynomialY, h3, h2, map_ofNat] <;> ring

/-- The derivative of `zxPoly` in the outer variable `x`. -/
def zxDeriv : Polynomial (Polynomial R) :=
  3 * Polynomial.X ^ 2 + 2 * C (C W.a₂) * Polynomial.X + C (C W.a₄ - C W.a₁ * Polynomial.X)

theorem derivative_zxPoly : derivative (zxPoly W) = zxDeriv W := by
  have h2 : derivative (C (Polynomial.X : Polynomial R) ^ 2) = 0 := by
    rw [← Polynomial.C_pow, Polynomial.derivative_C]
  simp [zxPoly, zxDeriv, h2, map_ofNat] <;> ring

theorem zxPoly_monic : (zxPoly W).Monic := by
  unfold zxPoly
  monicity!

theorem smooth_zy :
    RingHom.Smooth ((algebraMap (Chart W 2)
      (Localization.Away (zyEquiv W (AdjoinRoot.mk _ W.toAffine.polynomialY)))).comp
        (chartConst W 2)) := by
  have h := smooth_away_derivative W.toAffine.polynomial W.toAffine.monic_polynomial
  rw [derivative_affinePolynomial] at h
  exact smooth_transport (chartConst W 2) (zyEquiv W) (fun a => by exact presEquiv_algebraMap _ _ _ _ _ _ _ _ _ _ _ _ a) _ h

theorem smooth_zx :
    RingHom.Smooth ((algebraMap (Chart W 2)
      (Localization.Away (zxEquiv W (AdjoinRoot.mk _ (zxDeriv W))))).comp (chartConst W 2)) := by
  have h := smooth_away_derivative (zxPoly W) (zxPoly_monic W)
  rw [derivative_zxPoly] at h
  exact smooth_transport (chartConst W 2) (zxEquiv W) (fun a => by exact presEquiv_algebraMap _ _ _ _ _ _ _ _ _ _ _ _ a) _ h


section ZChart

variable [W.IsElliptic]

/-- On the `Z`-chart the two partial derivatives generate the unit ideal: a point with
values in a field where both vanish would be singular. -/
theorem span_partials_zChart :
    Ideal.span {zyEquiv W (AdjoinRoot.mk _ W.toAffine.polynomialY),
      zxEquiv W (AdjoinRoot.mk _ (zxDeriv W))} = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  let _ := Ideal.Quotient.field m
  let π := Ideal.Quotient.mk m
  let g : R →+* Chart W 2 ⧸ m := π.comp (chartConst W 2)
  let x := π (ratio W 2 0)
  let y := π (ratio W 2 1)
  have hzero (b : Chart W 2) (hb : b ∈ Ideal.span {zyEquiv W (AdjoinRoot.mk _ W.toAffine.polynomialY),
      zxEquiv W (AdjoinRoot.mk _ (zxDeriv W))}) : π b = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle hb)
  have hY := hzero _ (Ideal.subset_span (Set.mem_insert _ _))
  have hX := hzero _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  have heq : (W.map g).toAffine.Equation x y := by
    have h := congrArg π (chart_equation W 2)
    rw [map_zero, ← MvPolynomial.coe_eval₂Hom, ← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom,
      MvPolynomial.coe_eval₂Hom] at h
    simp only [Projective.polynomial, MvPolynomial.eval₂_add, MvPolynomial.eval₂_sub,
      MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X, MvPolynomial.eval₂_C,
      ratio_self, map_one] at h
    rw [Affine.equation_iff']
    simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
    linear_combination h
  have hns := (Affine.equation_iff_nonsingular (W := (W.map g).toAffine)).mp heq
  rw [Affine.Nonsingular, Affine.evalEval_polynomialX, Affine.evalEval_polynomialY] at hns
  rcases hns.2 with h | h
  · apply h
    have e1 : zxEquiv W (AdjoinRoot.mk _ (zxDeriv W)) = presLift W 2 (zxPoly W) (ratio W 2 1)
        (ratio W 2 0) (zx_eval W) (AdjoinRoot.mk _ (zxDeriv W)) := rfl
    rw [e1, presLift, AdjoinRoot.lift_mk] at hX
    simp only [zxDeriv, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_ofNat, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_sub, map_add, map_mul, map_pow, map_sub, map_ofNat] at hX
    simp only [map_a₁, map_a₂, map_a₄]
    linear_combination -hX
  · apply h
    have e2 : zyEquiv W (AdjoinRoot.mk _ W.toAffine.polynomialY) = presLift W 2
        W.toAffine.polynomial (ratio W 2 0) (ratio W 2 1) (zy_eval W)
        (AdjoinRoot.mk _ W.toAffine.polynomialY) := rfl
    rw [e2, presLift, AdjoinRoot.lift_mk] at hY
    simp only [Affine.polynomialY, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_ofNat, Polynomial.coe_eval₂RingHom,
      map_add, map_mul, map_ofNat] at hY
    simp only [map_a₁, map_a₃]
    linear_combination hY

/-- The `Z`-chart of the projective cubic is smooth over the base. -/
theorem smooth_chartZ : RingHom.Smooth (chartConst W 2) := by
  refine RingHom.Smooth.ofLocalizationSpanTarget (chartConst W 2) _ (span_partials_zChart W) ?_
  rintro ⟨r, hr⟩
  rcases hr with rfl | rfl
  · exact smooth_zy W
  · exact smooth_zx W

end ZChart

#print axioms smooth_away_derivative
#print axioms smooth_transport
#print axioms smooth_zy
#print axioms smooth_zx
#print axioms span_partials_zChart
#print axioms smooth_chartZ

end ZInQ.Manuscript.RC.ModelTarget
