import ZInQKernel.Contrib.OneProof.RC.ModelGeneric4.GenericSpecialization
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric4.ChartContinuity
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric4.PeriodContinuity
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric4.Density
import Mathlib.Topology.Algebra.MvPolynomial

/-! # The actual pair class at every parameter (item 1)

The marked lift of the analytic pair `(ℂ/(ℤτ + ℤ), ⟨1/N⟩)` to the pinned short cover evaluates the
five cover coordinates to `-g₂/4, -g₃/4, ℘(1/N), ℘'(1/N)/2, Δ⁻¹`, all continuous in τ. Its
restriction to the pinned rational quotient is the complex point of the actual analytic pair class.
The inverse evaluation of the finite chart is also continuous in τ. The two complex points agree at
every parameter with transcendental j-value, which are dense; hence they agree everywhere. -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric4

open LeafModCurves ModelGeneric ModelGeneric2 ModelTorsion RC.ModelInvariants UpperHalfPlane
open WeierstrassCurve.Affine
open ZInQ.Manuscript.RC

open private rationalLevel_isUnit from ZInQKernel.Contrib.OneProof.RC.ModelGeneric.Rational
open private ModelGeneric3.latticeGenerator from
  ZInQKernel.Contrib.OneProof.RC.ModelGeneric3.AnalyticPair
open private exactOrderPointOfGenerator_coordinates exactOrderPointOfGenerator_coefficients from
  ZInQKernel.Contrib.OneProof.RC.ModelLevels3.ExactOrderScaling

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.haveILetI false

private instance periodCurve_isElliptic (τ : ℍ) :
    (PeriodPair.ofTau τ).weierstrassCurve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (PeriodPair.ofTau τ).discriminant_ne_zero.weierstrassCurve_Δ_ne_zero⟩

private instance periodCurve_isShortNF (τ : ℍ) :
    (PeriodPair.ofTau τ).weierstrassCurve.IsShortNF := ⟨rfl, rfl, rfl⟩

/-- The marked lift of the analytic pair at τ to the pinned short cover: the classifying point of
the period curve of `ℤτ + ℤ` with the generator `u(1/N)`. -/
noncomputable def markedLift (n : ℕ) [NeZero (n + 2)] (τ : ℍ) : rationalCover (n + 2) →ₐ[ℚ] ℂ :=
  exactOrderPointOfGenerator rationalLevel_isUnit (PeriodPair.ofTau τ).weierstrassCurve
    (ModelGeneric3.latticeGenerator (N := n + 2) τ)

/-- The complex point of the pinned rational quotient obtained by restricting the marked lift. -/
noncomputable def analyticPoint {N : ℕ} [NeZero N] (h₂ : 2 ≤ N) (τ : ℍ) :
    Y0RationalAlgebra h₂ →ₐ[ℚ] ℂ := by
  obtain _ | _ | n := N
  · omega
  · omega
  · exact (markedLift n τ).comp (Y0RationalInclusion h₂)

/-- The restricted marked lift reads the actual analytic pair class. -/
theorem rationalPoints_analyticPoint {N : ℕ} [NeZero N] (h₂ : 2 ≤ N) (τ : ℍ) :
    rationalPoints h₂ (analyticPoint h₂ τ) = ModelGeneric3.analyticCyclicPair (N := N) τ := by
  obtain _ | _ | n := N
  · omega
  · omega
  change (rationalPointReading h₂).val ((markedLift n τ).comp (Y0RationalInclusion h₂)) = _
  rw [(rationalPointReading h₂).property, markedLift, shortCoverPair_marked]
  rfl

open private ModelGeneric3.nsmul_div_mem_periodLattice from
  ZInQKernel.Contrib.OneProof.RC.ModelGeneric3.AnalyticPair in
private theorem one_div_notMem (n : ℕ) [NeZero (n + 2)] (τ : ℍ) :
    (1 / ((n + 2 : ℕ) : ℂ)) ∉ (PeriodPair.ofTau τ).lattice := by
  intro h
  have h1 := (ModelGeneric3.nsmul_div_mem_periodLattice (N := n + 2) τ 1).1 (by rwa [one_smul])
  have := Nat.le_of_dvd one_pos h1
  omega

private theorem coefficientPoint_a₄ (W : WeierstrassCurve ℂ) [W.IsElliptic] [W.IsShortNF] :
    shortCoefficientPoint (R := ℚ) W (shortFamily ℚ).a₄ = W.a₄ :=
  congrArg WeierstrassCurve.a₄ (shortFamily_map_coefficientPoint (R := ℚ) W)

private theorem coefficientPoint_a₆ (W : WeierstrassCurve ℂ) [W.IsElliptic] [W.IsShortNF] :
    shortCoefficientPoint (R := ℚ) W (shortFamily ℚ).a₆ = W.a₆ :=
  congrArg WeierstrassCurve.a₆ (shortFamily_map_coefficientPoint (R := ℚ) W)

private theorem coefficientPoint_invSelf (W : WeierstrassCurve ℂ) [W.IsElliptic] [W.IsShortNF] :
    shortCoefficientPoint (R := ℚ) W (IsLocalization.Away.invSelf (shortEquation ℚ).Δ) =
      W.Δ⁻¹ := by
  let c := shortCoefficientPoint (R := ℚ) W
  have hΔ : c (algebraMap (MvPolynomial (Fin 2) ℚ) (ShortBase ℚ) (shortEquation ℚ).Δ) = W.Δ := by
    have h := congrArg WeierstrassCurve.Δ (shortFamily_map_coefficientPoint (R := ℚ) W)
    rw [WeierstrassCurve.map_Δ, shortFamily, WeierstrassCurve.map_Δ] at h
    exact h
  have hmul : c (IsLocalization.Away.invSelf (shortEquation ℚ).Δ) *
      c (algebraMap (MvPolynomial (Fin 2) ℚ) (ShortBase ℚ) (shortEquation ℚ).Δ) = 1 := by
    rw [← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]
  rw [hΔ] at hmul
  exact eq_inv_of_mul_eq_one_left hmul

/-- Each cover coordinate of the marked lift is continuous in τ. -/
theorem continuous_markedLift_coordinate (n : ℕ) [NeZero (n + 2)] (i : Fin 5) :
    Continuous fun τ : ℍ =>
      markedLift n τ (exactOrderShortCoordinates (R := ℚ) rationalLevel_isUnit i) := by
  have hN : 2 ≤ n + 2 := by omega
  have hcoeff (τ : ℍ) (a : ShortBase ℚ) : markedLift n τ (algebraMap (ShortBase ℚ) _ a) =
      shortCoefficientPoint (R := ℚ) (PeriodPair.ofTau τ).weierstrassCurve a :=
    exactOrderPointOfGenerator_coefficients rationalLevel_isUnit _ _ a
  have key : ∀ (τ : ℍ) (P : Generators (PeriodPair.ofTau τ).weierstrassCurve.toAffine.Point (n + 2))
      (x y : ℂ) (h : (PeriodPair.ofTau τ).weierstrassCurve.toAffine.Nonsingular x y),
      P.1 = Point.some x y h →
      exactOrderPointOfGenerator rationalLevel_isUnit (PeriodPair.ofTau τ).weierstrassCurve P
          (exactOrderX (shortFamily ℚ) rationalLevel_isUnit) = x ∧
        exactOrderPointOfGenerator rationalLevel_isUnit (PeriodPair.ofTau τ).weierstrassCurve P
          (exactOrderY (shortFamily ℚ) rationalLevel_isUnit) = y := by
    rintro τ ⟨P, hP⟩ x y h rfl
    exact exactOrderPointOfGenerator_coordinates rationalLevel_isUnit _ h hP
  have hxy (τ : ℍ) := key τ (ModelGeneric3.latticeGenerator (N := n + 2) τ) _ _ _
    ((PeriodPair.ofTau τ).toPoint_of_notMem (PeriodPair.ofTau τ).discriminant_ne_zero
      (one_div_notMem n τ))
  fin_cases i
  · change Continuous fun τ : ℍ =>
      markedLift n τ (algebraMap (ShortBase ℚ) _ (shortFamily ℚ).a₄)
    simp_rw [hcoeff, coefficientPoint_a₄]
    exact (continuous_g₂.neg.div_const 4).congr fun τ => rfl
  · change Continuous fun τ : ℍ =>
      markedLift n τ (algebraMap (ShortBase ℚ) _ (shortFamily ℚ).a₆)
    simp_rw [hcoeff, coefficientPoint_a₆]
    exact (continuous_g₃.neg.div_const 4).congr fun τ => rfl
  · change Continuous fun τ : ℍ => markedLift n τ (exactOrderX (shortFamily ℚ) rationalLevel_isUnit)
    exact (continuous_weierstrassP hN).congr fun τ => (hxy τ).1.symm
  · change Continuous fun τ : ℍ => markedLift n τ (exactOrderY (shortFamily ℚ) rationalLevel_isUnit)
    exact ((continuous_derivWeierstrassP hN).div_const 2).congr fun τ => (hxy τ).2.symm
  · change Continuous fun τ : ℍ => markedLift n τ
      (algebraMap (ShortBase ℚ) _ (IsLocalization.Away.invSelf (shortEquation ℚ).Δ))
    simp_rw [hcoeff, coefficientPoint_invSelf, PeriodPair.weierstrassCurve_Δ]
    exact (((continuous_g₂.pow 3).sub ((continuous_g₃.pow 2).const_mul 27)).inv₀
      fun τ => (PeriodPair.ofTau τ).discriminant_ne_zero)

/-- The marked lift is continuous in τ on every element of the cover. -/
theorem continuous_markedLift (n : ℕ) [NeZero (n + 2)] (s : rationalCover (n + 2)) :
    Continuous fun τ : ℍ => markedLift n τ s := by
  obtain ⟨m, rfl⟩ := exactOrderShortPresentation_surjective (R := ℚ) rationalLevel_isUnit s
  have h (τ : ℍ) : markedLift n τ (exactOrderShortPresentation rationalLevel_isUnit m) =
      MvPolynomial.eval (fun i => markedLift n τ
        (exactOrderShortCoordinates (R := ℚ) rationalLevel_isUnit i))
        (MvPolynomial.map (algebraMap ℚ ℂ) m) := by
    change ((markedLift n τ).comp (MvPolynomial.aeval (exactOrderShortCoordinates
      (R := ℚ) rationalLevel_isUnit))) m = _
    rw [MvPolynomial.comp_aeval, MvPolynomial.aeval_def, MvPolynomial.eval_map]
  simp_rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun i => continuous_markedLift_coordinate n i)

theorem continuous_analyticPoint {N : ℕ} [NeZero N] (h₂ : 2 ≤ N) (a : Y0RationalAlgebra h₂) :
    Continuous fun τ : ℍ => analyticPoint h₂ τ a := by
  obtain _ | _ | n := N
  · omega
  · omega
  exact continuous_markedLift n (Y0RationalInclusion h₂ a)

/-- **Item 1: the actual pair class at every parameter.** For every upper half-plane parameter τ,
including parameters where `j(τ)` is algebraic and the two coordinates of the finite chart
collide, the pinned rational reading of the complex point at τ is the actual analytic class
`(ℂ/(ℤτ + ℤ), ⟨1/N⟩)`. -/
theorem rationalPoints_rationalPointAtParameter {N : ℕ} [NeZero N] (h₂ : 2 ≤ N) (τ : ℍ) :
    rationalPoints h₂ (ModelGeneric3.rationalPointAtParameter h₂ τ) =
      ModelGeneric3.analyticCyclicPair (N := N) τ := by
  have hfun : ModelGeneric3.rationalPointAtParameter h₂ τ = analyticPoint h₂ τ := by
    ext a
    have h := Continuous.ext_on dense_transcendental_analyticJ
      (continuous_rationalPointAtParameter h₂ a) (continuous_analyticPoint h₂ a)
      (fun σ hσ => by
        have h1 := rationalPoints_rationalPointAtParameter_of_transcendental h₂ σ hσ
        have h2 := rationalPoints_analyticPoint h₂ σ
        have := (rationalPoints h₂).injective (h1.trans h2.symm)
        exact DFunLike.congr_fun this a)
    exact congrFun h τ
  rw [hfun, rationalPoints_analyticPoint]

#print axioms markedLift
#print axioms rationalPoints_analyticPoint
#print axioms continuous_markedLift
#print axioms rationalPoints_rationalPointAtParameter

end WeierstrassCurve.ModelLevels.ModelGeneric4
