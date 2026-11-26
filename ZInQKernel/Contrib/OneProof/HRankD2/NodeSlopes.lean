import ZInQKernel.Contrib.OneProof.HRankD2.LSeriesHasseWeil

/-!
# Split multiplicative reduction: the tangent slopes at the node

Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed. (GTM 106, Springer, 2009), §VII.5,
calls multiplicative reduction split when the slopes of the tangent lines at the node of the
reduced curve lie in the residue field, and §III.1 describes the tangent lines
at a singular point `(x₀, y₀)` through the quadratic part of the Taylor expansion of the
Weierstrass polynomial there.

Mathlib's `HasSplitMultiplicativeReduction` asks instead that the polynomial
`c₄ T² + a₁ c₄ T - (54 b₆ - 3 b₂ b₄ + a₂ c₄)` (`tangentPolynomial`) split over the residue field.
This file proves that the two tests agree, in every characteristic:

* `taylor_of_singular`: at a singular point, the Weierstrass polynomial is
  `(y - y₀)² + a₁ (x - x₀)(y - y₀) - (3x₀ + a₂)(x - x₀)² - (x - x₀)³`, so the tangent lines are
  `y - y₀ = α (x - x₀)` with `α² + a₁ α - (3x₀ + a₂) = 0` (`nodeSlopePolynomial`);
* `c₄_mul_x_of_singular`: `c₄ x₀ = 18 b₆ - b₂ b₄` at a singular point;
* `tangentPolynomial_eq_of_singular`: `tangentPolynomial W = c₄ · nodeSlopePolynomial W x₀`;
* `splits_tangentPolynomial_iff_exists_slope`: if `c₄ ≠ 0` (a node), the tangent polynomial
  splits if and only if a tangent slope lies in the field (and then both do);
* `hasSplitMultiplicativeReduction_iff_slope` and `hwSplit_iff_exists_slope`: the same for
  Mathlib's reduction type and for the test in `hwEulerPoly`.
-/

set_option autoImplicit false

namespace ZInQ.Manuscript.RankModel

open Polynomial WeierstrassCurve

section Field

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- The polynomial `T² + a₁ T - (3x₀ + a₂)` whose roots are the slopes of the tangent lines at
a singular point with abscissa `x₀`. -/
noncomputable def nodeSlopePolynomial (x₀ : F) : F[X] :=
  X ^ 2 + C W.a₁ * X - C (3 * x₀ + W.a₂)

variable {W}

/-- The Taylor expansion of the Weierstrass polynomial at a singular point `(x₀, y₀)`: no
constant and no linear term, quadratic part `v² + a₁ u v - (3x₀ + a₂) u²`. -/
theorem taylor_of_singular {x₀ y₀ : F} (hE : W.toAffine.Equation x₀ y₀)
    (hs : ¬ W.toAffine.Nonsingular x₀ y₀) (u v : F) :
    (y₀ + v) ^ 2 + W.a₁ * (x₀ + u) * (y₀ + v) + W.a₃ * (y₀ + v) -
      ((x₀ + u) ^ 3 + W.a₂ * (x₀ + u) ^ 2 + W.a₄ * (x₀ + u) + W.a₆) =
      v ^ 2 + W.a₁ * u * v - (3 * x₀ + W.a₂) * u ^ 2 - u ^ 3 := by
  rw [Affine.nonsingular_iff'] at hs
  push Not at hs
  obtain ⟨hX, hY⟩ := hs hE
  rw [Affine.equation_iff'] at hE
  linear_combination hE + u * hX + v * hY

/-- At a singular point, `c₄ x₀ = 18 b₆ - b₂ b₄` (the abscissa of the node used in
Mathlib's derivation of the tangent polynomial). -/
theorem c₄_mul_x_of_singular {x₀ y₀ : F} (hE : W.toAffine.Equation x₀ y₀)
    (hs : ¬ W.toAffine.Nonsingular x₀ y₀) : W.c₄ * x₀ = 18 * W.b₆ - W.b₂ * W.b₄ := by
  rw [Affine.nonsingular_iff'] at hs
  push Not at hs
  obtain ⟨hX, hY⟩ := hs hE
  rw [Affine.equation_iff'] at hE
  simp only [c₄, b₂, b₄, b₆]
  linear_combination (-18 * (2 * y₀ + W.a₁ * x₀ + W.a₃) +
      (W.a₁ ^ 2 + 4 * W.a₂ + 12 * x₀) * W.a₁) * hY + 72 * hE -
    2 * (W.a₁ ^ 2 + 4 * W.a₂ + 12 * x₀) * hX

/-- At a singular point, Mathlib's tangent polynomial is `c₄` times the slope polynomial. -/
theorem tangentPolynomial_eq_of_singular {x₀ y₀ : F} (hE : W.toAffine.Equation x₀ y₀)
    (hs : ¬ W.toAffine.Nonsingular x₀ y₀) :
    tangentPolynomial W = C W.c₄ * nodeSlopePolynomial W x₀ := by
  have h : 54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄ = W.c₄ * (3 * x₀ + W.a₂) := by
    linear_combination -3 * c₄_mul_x_of_singular hE hs
  rw [tangentPolynomial, nodeSlopePolynomial, h]
  simp only [map_mul]
  ring

theorem degree_nodeSlopePolynomial (x₀ : F) : (nodeSlopePolynomial W x₀).degree = 2 := by
  unfold nodeSlopePolynomial
  compute_degree!

/-- The slope polynomial splits if and only if one tangent slope lies in the field. -/
theorem splits_nodeSlopePolynomial_iff (x₀ : F) :
    (nodeSlopePolynomial W x₀).Splits ↔ ∃ α : F, α ^ 2 + W.a₁ * α - (3 * x₀ + W.a₂) = 0 := by
  constructor
  · intro h
    obtain ⟨α, hα⟩ := h.exists_eval_eq_zero (by rw [degree_nodeSlopePolynomial]; decide)
    exact ⟨α, by simpa [nodeSlopePolynomial] using hα⟩
  · rintro ⟨α, hα⟩
    have hq : nodeSlopePolynomial W x₀ = (X - C α) * (X - C (-W.a₁ - α)) := by
      have hc : 3 * x₀ + W.a₂ = α ^ 2 + W.a₁ * α := by linear_combination -hα
      rw [nodeSlopePolynomial, hc]
      simp only [map_add, map_mul, map_pow, map_neg, map_sub]
      ring
    rw [hq]
    exact (Splits.X_sub_C _).mul (Splits.X_sub_C _)

/-- **Node slopes.** At a node `(x₀, y₀)` (a singular point with `c₄ ≠ 0`), Mathlib's tangent
polynomial splits if and only if a slope of a tangent line at the node lies in the field. -/
theorem splits_tangentPolynomial_iff_exists_slope {x₀ y₀ : F} (hE : W.toAffine.Equation x₀ y₀)
    (hs : ¬ W.toAffine.Nonsingular x₀ y₀) (hc : W.c₄ ≠ 0) :
    (tangentPolynomial W).Splits ↔ ∃ α : F, α ^ 2 + W.a₁ * α - (3 * x₀ + W.a₂) = 0 := by
  rw [tangentPolynomial_eq_of_singular hE hs, splits_mul_iff_right (by simpa using hc)
    (Splits.C _), splits_nodeSlopePolynomial_iff]

end Field

section Local

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- On a minimal equation with multiplicative reduction, the reduction has `c₄ ≠ 0`. -/
theorem c₄_reduction_ne_zero (W : WeierstrassCurve K) [h : HasMultiplicativeReduction R W] :
    (W.reduction R).c₄ ≠ 0 := by
  have hm := h.multiplicativeReduction
  rw [← integralModel_c₄_eq R W, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff] at hm
  rw [reduction, map_c₄, Ne, IsLocalRing.residue_eq_zero_iff]
  exact hm

/-- **Split multiplicative reduction in Silverman's sense.** For a minimal equation and a
singular point `(x₀, y₀)` of its reduction, Mathlib's split multiplicative reduction holds if
and only if the reduction is multiplicative and a slope of a tangent line at the node lies in
the residue field. -/
theorem hasSplitMultiplicativeReduction_iff_slope (W : WeierstrassCurve K) [IsMinimal R W]
    {x₀ y₀ : IsLocalRing.ResidueField R} (hE : (W.reduction R).toAffine.Equation x₀ y₀)
    (hs : ¬ (W.reduction R).toAffine.Nonsingular x₀ y₀) :
    HasSplitMultiplicativeReduction R W ↔ HasMultiplicativeReduction R W ∧
      ∃ α, α ^ 2 + (W.reduction R).a₁ * α - (3 * x₀ + (W.reduction R).a₂) = 0 := by
  rw [hasSplitMultiplicativeReduction_iff_residue]
  constructor
  · rintro ⟨hm, hsp⟩
    exact ⟨hm, (splits_tangentPolynomial_iff_exists_slope hE hs
      (c₄_reduction_ne_zero (R := R) W)).mp hsp⟩
  · rintro ⟨hm, hα⟩
    exact ⟨hm, (splits_tangentPolynomial_iff_exists_slope hE hs
      (c₄_reduction_ne_zero (R := R) W)).mpr hα⟩

end Local

/-- The splitting test in `hwEulerPoly`, read as Silverman's: if `p` is prime, `p ∤ c₄` and
`(x₀, y₀)` is a singular point of `E₀ mod p`, the test holds if and only if a slope of a
tangent line at the node lies in `𝔽_p`. -/
theorem hwSplit_iff_exists_slope (E₀ : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    (hc : ¬ (p : ℤ) ∣ E₀.c₄) {x₀ y₀ : ZMod p}
    (hE : (hwReduction E₀ p).toAffine.Equation x₀ y₀)
    (hs : ¬ (hwReduction E₀ p).toAffine.Nonsingular x₀ y₀) :
    (tangentPolynomial (hwReduction E₀ p)).Splits ↔
      ∃ α : ZMod p, α ^ 2 + (E₀.a₁ : ZMod p) * α - (3 * x₀ + (E₀.a₂ : ZMod p)) = 0 := by
  have hc' : (hwReduction E₀ p).c₄ ≠ 0 := by
    rw [hwReduction, map_c₄, eq_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hc
  rw [splits_tangentPolynomial_iff_exists_slope hE hs hc']
  simp [hwReduction]

end ZInQ.Manuscript.RankModel
