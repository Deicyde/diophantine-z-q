import ZInQKernel.Contrib.RC53Assist.HodgeLineBinding.HodgeLine
import ZInQKernel.Contrib.RC53Assist.HodgeLineBinding.CurveExpansion
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Non-vacuity of the evaluation in the Hodge line

* The evaluation of Kähler differentials at a rational point is not degenerate: on the power
  series ring `ℚ⟦X⟧` with the constant coefficient as value map, `dX` evaluates to the nonzero
  class of `X` in `𝔪/𝔪²` (`pointEval_powerSeries_D_X_ne_zero`).
* The expansion of the invariant differential at infinity and the local parameter `-x/y` apply to
  an actual nonsingular curve, `y² = x³ - x` over `ℚ` (`curveYXX_invariant_expansion`,
  `curveYXX_paramZ`).
* The main theorems hold in the number-field world over `ℚ` itself
  (`exists_weierstrassModel_hodgeEval_rat`, `finrank_hodgeSpace_one_rat`).

No one-dimensional abelian variety is constructed as a group scheme in the library, so the full
hypotheses (an abelian variety and a smooth group model) are not instantiated by a concrete
object; the Weierstrass data are produced for every such object by the number-field S2a theorem
(`exists_weierstrassModel_hodgeEval`).
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.HodgeLineBinding

open CategoryTheory KaehlerDifferential IsLocalRing PowerSeries
open ZInQ.DefFaltings ZInQ.Contrib.RC53Assist.S2aNumberField
open ZInQ.Contrib.RC53Assist.AbelianCurve (functionFieldAlgebra abelian_scheme_integral)

section PowerSeries

/-- THEOREM (proved). The constant coefficient is a retraction of the constants of `ℚ⟦X⟧`.
Locator: Mathlib, `PowerSeries.constantCoeff_C`. -/
theorem constantCoeff_algebraMap (c : ℚ) :
    constantCoeff (algebraMap ℚ ℚ⟦X⟧ c) = c := by
  rw [PowerSeries.algebraMap_eq, constantCoeff_C]

/-- THEOREM (proved). `X` lies in the maximal ideal of `ℚ⟦X⟧`. Locator: Mathlib,
`PowerSeries.maximalIdeal_eq_span_X`. -/
theorem X_mem_maximalIdeal : (X : ℚ⟦X⟧) ∈ maximalIdeal ℚ⟦X⟧ := by
  rw [PowerSeries.maximalIdeal_eq_span_X]
  exact Ideal.subset_span rfl

/-- THEOREM (proved). `X` is not in the square of the maximal ideal of `ℚ⟦X⟧`.
Locator: Mathlib, `PowerSeries.maximalIdeal_eq_span_X`, `PowerSeries.X_prime`. -/
theorem X_not_mem_maximalIdeal_sq : (X : ℚ⟦X⟧) ∉ maximalIdeal ℚ⟦X⟧ ^ 2 := by
  rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  rintro ⟨f, hf⟩
  have hX : (X : ℚ⟦X⟧) ≠ 0 := X_ne_zero
  have h1 : (X : ℚ⟦X⟧) * 1 = X * (X * f) := by rw [mul_one, ← mul_assoc, ← pow_two]; exact hf
  have h2 := mul_left_cancel₀ hX h1
  exact X_prime.not_isUnit (isUnit_iff_exists_inv.mpr ⟨f, h2.symm⟩)

/-- THEOREM (proved, non-vacuity). On `ℚ⟦X⟧` the evaluation of `dX` at the rational point
`X = 0` is the class of `X`, which is nonzero. Locator: `pointEval_D_of_mem`. -/
theorem pointEval_powerSeries_D_X_ne_zero :
    pointEval (constantCoeff (R := ℚ)) constantCoeff_algebraMap (D ℚ ℚ⟦X⟧ X) ≠ 0 := by
  rw [pointEval_D_of_mem _ _ X_mem_maximalIdeal]
  intro h
  exact X_not_mem_maximalIdeal_sq ((Ideal.toCotangent_eq_zero _ _).mp h)

end PowerSeries

section Curve

/-- DEFINITION. The Weierstrass curve `y² = x³ - x` over `ℚ`. Locator: Silverman, *The Arithmetic
of Elliptic Curves*, second edition, III.1. -/
def curveYXX : WeierstrassCurve ℚ := ⟨0, 0, 0, -1, 0⟩

/-- THEOREM (proved). The discriminant of `y² = x³ - x` is `64`. Locator: Mathlib,
`WeierstrassCurve.Δ`. -/
theorem curveYXX_Δ : curveYXX.Δ = 64 := by
  simp only [curveYXX, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num

/-- INSTANCE (proved). The curve `y² = x³ - x` over `ℚ` is nonsingular. Locator: `curveYXX_Δ`;
Mathlib, `WeierstrassCurve.IsElliptic`. -/
instance curveYXX_isElliptic : curveYXX.IsElliptic :=
  ⟨by rw [curveYXX_Δ]; exact isUnit_iff_ne_zero.mpr (by norm_num)⟩

/-- THEOREM (proved, non-vacuity). The expansion `ω = u⁻¹ • d(-x/y)` holds on the function field
of `y² = x³ - x`, with `u ≠ 0`. Locator: `invariantDifferential_eq_localUnit_inv_smul`. -/
theorem curveYXX_invariant_expansion :
    WeierstrassCurve.Affine.invariantDifferential curveYXX.toAffine =
        (localUnit curveYXX (-curveYXX.toAffine.genericX / curveYXX.toAffine.genericY)
          (-1 / curveYXX.toAffine.genericY))⁻¹ •
          D ℚ curveYXX.toAffine.FunctionField
            (-curveYXX.toAffine.genericX / curveYXX.toAffine.genericY) ∧
      localUnit curveYXX (-curveYXX.toAffine.genericX / curveYXX.toAffine.genericY)
          (-1 / curveYXX.toAffine.genericY) ≠ 0 :=
  ⟨invariantDifferential_eq_localUnit_inv_smul curveYXX, localUnit_genericPoint_ne_zero curveYXX⟩

/-- THEOREM (proved, non-vacuity). On the projective model of `y² = x³ - x`, `-x/y` is a local
parameter at `O`: it lies in `𝔪_O` and not in `𝔪_O²`. Locator: `paramZ_mem`,
`paramZ_not_mem_sq`. -/
theorem curveYXX_paramZ :
    paramZ curveYXX ∈
        maximalIdeal ((AlgebraicGeometry.Proj curveYXX.toProjective.grading).presheaf.stalk
          (pointO curveYXX)) ∧
      paramZ curveYXX ∉
        maximalIdeal ((AlgebraicGeometry.Proj curveYXX.toProjective.grading).presheaf.stalk
          (pointO curveYXX)) ^ 2 :=
  ⟨paramZ_mem curveYXX, paramZ_not_mem_sq curveYXX⟩

end Curve

section Rational

/-- THEOREM (proved, non-vacuity). The existence form of the main theorem over `ℚ`. Locator:
`exists_weierstrassModel_hodgeEval`. -/
theorem exists_weierstrassModel_hodgeEval_rat (E : PkgI3.AbVar ℚ) (G : GroupModel E ℚ)
    (hdim : E.dim = 1) :
    letI := abelian_scheme_integral (E.baseChange ℚ).X
    letI := functionFieldAlgebra (E.baseChange ℚ).X.hom
    ∃ E' : WeierstrassCurve ℚ, E'.IsElliptic ∧
      ∃ (e : E'.toAffine.FunctionField ≃ₐ[ℚ] (E.baseChange ℚ).X.left.functionField)
        (i : (E.baseChange ℚ).X.left ≅ AlgebraicGeometry.Proj E'.toProjective.grading),
        i.hom ≫ projectiveStructure E' = (E.baseChange ℚ).X.hom ∧
        i.hom.functionFieldMap.hom = e.toRingHom.comp (projFunctionFieldEquiv E').toRingHom ∧
        ∃ hO : i.hom (identityPoint (E.baseChange ℚ).X) = pointO E',
          ∃ hreg : kaehlerTransport e (WeierstrassCurve.Affine.invariantDifferential E'.toAffine)
              ∈ regularAtOrigin (E.baseChange ℚ),
            hodgeEval G hdim ⟨_, hreg⟩ = G.wedge ![originParameter G E' i hO] ∧
            G.wedge ![originParameter G E' i hO] ≠ 0 :=
  exists_weierstrassModel_hodgeEval G hdim

/-- THEOREM (proved, non-vacuity). Over `ℚ`, the Hodge space `hodgeSpace 1` of a smooth group
model of a one-dimensional abelian variety is a line. Locator:
`finrank_hodgeSpace_one_of_dim_one`. -/
theorem finrank_hodgeSpace_one_rat (E : PkgI3.AbVar ℚ) (G : GroupModel E ℚ) (hdim : E.dim = 1) :
    Module.finrank ℚ (G.hodgeSpace 1) = 1 :=
  finrank_hodgeSpace_one_of_dim_one G hdim

end Rational

end ZInQ.Contrib.RC53Assist.HodgeLineBinding
