/-
The separable decomposition-fixed field inside the given ambient field.
This definition retains the original valuation and its decomposition group;
it does not identify an imperfect full fixed field with a separable field.
-/
import Mathlib

set_option autoImplicit false
noncomputable section
universe u v

namespace ZInQ.Contrib.CloudR2Raynaud.StrictHenselization

/-- The ordinary field is the literal meet of the decomposition-fixed
    field and the separable closure, in this order. -/
def henselizationField {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
    (w : ValuationSubring Ω) : IntermediateField K Ω :=
  IntermediateField.fixedField (w.decompositionSubgroup K) ⊓ separableClosure K Ω

end ZInQ.Contrib.CloudR2Raynaud.StrictHenselization
