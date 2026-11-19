import ZInQKernel.Contrib.RC53Assist.AbelianCurveInputs.ComplexDifferentialLine

/-!
# Concrete inverse-parameter checks of the normalized comparison

These checks use X and X inverse in the actual rational function field over the
complex numbers. The uniformizer logarithmic residue is one, and the two
independently constructed normalized comparisons agree.

Locators: Stichtenoth I.2 and I.7; the closed normalization and chain rule in
`CanonicalResidues.lean`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.AbelianCurveInputs.NormalizedExamples

open Module TauCeti Polynomial KaehlerDifferential
open scoped IntermediateField

/-- THEOREM. The normalized cotraces at X and X inverse obey the nontrivial
inverse chain rule over the complex numbers.
Locator: the closed chain rule and the Kähler inverse Leibniz identity. -/
theorem rational_inverse_chain_rule :
    let hx := RatFunc.transcendental_X (K := ℂ)
    let hy := uniformizer_transcendental (Place.infty ℂ) (Place.isUniformizer_infty (k := ℂ))
    letI := (IsFunctionField.ratFunc ℂ).finiteDimensional_adjoin hx
    letI := (IsFunctionField.ratFunc ℂ).finiteDimensional_adjoin hy
    letI := weilDifferentialSpaceModule (IsFunctionField.ratFunc ℂ)
    differentialOfSeparating (IsFunctionField.ratFunc ℂ) hy =
      (-(RatFunc.X : RatFunc ℂ)⁻¹ ^ 2) •
        differentialOfSeparating (IsFunctionField.ratFunc ℂ) hx := by
  let hx := RatFunc.transcendental_X (K := ℂ)
  let hy := uniformizer_transcendental (Place.infty ℂ) (Place.isUniformizer_infty (k := ℂ))
  haveI := (IsFunctionField.ratFunc ℂ).finiteDimensional_adjoin hx
  haveI := (IsFunctionField.ratFunc ℂ).finiteDimensional_adjoin hy
  letI := weilDifferentialSpaceModule (IsFunctionField.ratFunc ℂ)
  have hd : derivativeOfSeparating hx (RatFunc.X : RatFunc ℂ)⁻¹ =
      -(RatFunc.X : RatFunc ℂ)⁻¹ ^ 2 := by
    rw [Derivation.leibniz_inv, derivativeOfSeparating_self, smul_eq_mul, mul_one]
  have h := CanonicalResidues.separatingCotraceChainRule ℂ (RatFunc ℂ)
    (IsFunctionField.ratFunc ℂ) isIntegrallyClosedIn_ratFunc RatFunc.X RatFunc.X⁻¹ hx hy
  rw [hd] at h
  exact h

/-- THEOREM. The logarithmic residue of d(X inverse) at infinity, evaluated on
X, is one. In particular the local functional is nonzero.
Locator: the closed uniformizer normalization and the degree-one place at infinity. -/
theorem rational_inverse_uniformizer_residue :
    let hx := RatFunc.transcendental_X (K := ℂ)
    letI := (IsFunctionField.ratFunc ℂ).finiteDimensional_adjoin hx
    letI := weilDifferentialSpaceModule (IsFunctionField.ratFunc ℂ)
    repartitionDualComponent (comparison (IsFunctionField.ratFunc ℂ)
      isIntegrallyClosedIn_ratFunc hx (D ℂ (RatFunc ℂ) RatFunc.X⁻¹) :
        Module.Dual ℂ ↥(repartitionSpace ℂ (RatFunc ℂ))) (Place.infty ℂ) RatFunc.X = 1 := by
  let hx := RatFunc.transcendental_X (K := ℂ)
  haveI := (IsFunctionField.ratFunc ℂ).finiteDimensional_adjoin hx
  letI := weilDifferentialSpaceModule (IsFunctionField.ratFunc ℂ)
  have h := CanonicalResidues.uniformizer_logarithmic_normalization
    (IsFunctionField.ratFunc ℂ) isIntegrallyClosedIn_ratFunc hx (Place.infty ℂ)
    (Place.isUniformizer_infty (k := ℂ))
  simpa only [inv_inv, Place.degree_infty, Nat.cast_one] using h

/-- THEOREM. The normalized comparisons constructed at X and X inverse are
literally equal, not merely proportional by an unspecified constant.
Locator: the closed parameter-independent comparison theorem. -/
theorem rational_inverse_parameter_independence :
    let hx := RatFunc.transcendental_X (K := ℂ)
    let hy := uniformizer_transcendental (Place.infty ℂ) (Place.isUniformizer_infty (k := ℂ))
    letI := (IsFunctionField.ratFunc ℂ).finiteDimensional_adjoin hx
    letI := (IsFunctionField.ratFunc ℂ).finiteDimensional_adjoin hy
    letI := weilDifferentialSpaceModule (IsFunctionField.ratFunc ℂ)
    comparison (IsFunctionField.ratFunc ℂ) isIntegrallyClosedIn_ratFunc hx =
      comparison (IsFunctionField.ratFunc ℂ) isIntegrallyClosedIn_ratFunc hy :=
  comparison_parameter_independent CanonicalResidues.separatingCotraceChainRule ℂ (RatFunc ℂ)
    (IsFunctionField.ratFunc ℂ) isIntegrallyClosedIn_ratFunc RatFunc.X RatFunc.X⁻¹
    (RatFunc.transcendental_X (K := ℂ))
    (uniformizer_transcendental (Place.infty ℂ) (Place.isUniformizer_infty (k := ℂ)))

end ZInQ.Contrib.RC53Assist.AbelianCurveInputs.NormalizedExamples
