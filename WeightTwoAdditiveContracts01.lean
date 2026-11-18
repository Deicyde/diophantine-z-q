import WeightTwoAdditiveSplitting04

/-!
# Literal arbitrary-form contracts for the additive weight-two decomposition

These contracts have no rationality, integrality, profile-surjectivity,
residue, or orthogonality hypothesis. The level-three and composite-level
instances are ordinary specializations of the proved general result.
-/

noncomputable section
set_option autoImplicit false
open Complex Matrix ModularForm
open scoped MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.WeightTwoAdditive

open ZInQ.Contrib.HeckePrimeRationality

/-- All levels at least three, with the positive-level instance supplied rather than assumed. -/
theorem every_weight_two_form (N : ℕ) (hN : 3 ≤ N)
    (f : ModularForm (WeightTwoConstants.principalLevel N) 2) :
    ∃ E : ModularForm (WeightTwoConstants.principalLevel N) 2,
      E ∈ DivisionSeriesMembership.divisionSpan N (by omega) ∧
      E ∈ TorsionQuadraticGenerators.productSpan N (by omega) ∧
      ∃ g : CuspForm (WeightTwoConstants.principalLevel N) 2,
        f = E + (g : ModularForm (WeightTwoConstants.principalLevel N) 2) := by
  let : NeZero N := ⟨by omega⟩
  exact actual_division_product_plus_cusp N hN f

/-- An arbitrary actual level-three form, not an assumed integral-coefficient form. -/
theorem every_level_three_weight_two_form
    (f : ModularForm (WeightTwoConstants.principalLevel 3) 2) :
    ∃ E : ModularForm (WeightTwoConstants.principalLevel 3) 2,
      E ∈ DivisionSeriesMembership.divisionSpan 3 (by norm_num) ∧
      E ∈ TorsionQuadraticGenerators.productSpan 3 (by norm_num) ∧
      ∃ g : CuspForm (WeightTwoConstants.principalLevel 3) 2,
        f = E + (g : ModularForm (WeightTwoConstants.principalLevel 3) 2) :=
  every_weight_two_form 3 (by norm_num) f

/-- The composite even level is included without classifying its full centre as only two scalars. -/
theorem every_level_eight_weight_two_form
    (f : ModularForm (WeightTwoConstants.principalLevel 8) 2) :
    ∃ E : ModularForm (WeightTwoConstants.principalLevel 8) 2,
      E ∈ DivisionSeriesMembership.divisionSpan 8 (by norm_num) ∧
      E ∈ TorsionQuadraticGenerators.productSpan 8 (by norm_num) ∧
      ∃ g : CuspForm (WeightTwoConstants.principalLevel 8) 2,
        f = E + (g : ModularForm (WeightTwoConstants.principalLevel 8) 2) :=
  every_weight_two_form 8 (by norm_num) f

#print axioms every_weight_two_form
#print axioms every_level_three_weight_two_form
#print axioms every_level_eight_weight_two_form

end ZInQ.Contrib.HeckePrimeRationality.WeightTwoAdditive
