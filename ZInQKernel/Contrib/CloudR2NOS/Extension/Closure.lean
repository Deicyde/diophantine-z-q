module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Algebraic

/-!
# The original geometric closure is also a closure of an intermediate field

New standard-library join for the NOS assembly. It retains the SAME Ω and
algebra maps: algebraicity over the lower field implies algebraicity over
an intermediate field, while Ω is already algebraically closed.
No perfectness, separability, characteristic or finite-degree hypothesis
is added. This does not construct a valuation, a model or good descent.
-/

public section

universe u v w

namespace ZInQ.Contrib.CloudR2NOS.Extension

/-- An algebraic closure of the bottom field remains an algebraic closure of
any intermediate field in the same algebra tower, without changing Ω. -/
theorem isAlgClosure_of_tower
    {K : Type u} {E : Type v} {Ω : Type w} [Field K] [Field E] [Field Ω]
    [Algebra K E] [Algebra E Ω] [Algebra K Ω] [IsScalarTower K E Ω]
    [IsAlgClosure K Ω] : IsAlgClosure E Ω := by
  exact ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) E⟩

/-- The literal original algebraic closure, regarded over a field inside it. -/
theorem isAlgClosure_over_intermediateField (K : Type u) [Field K]
    (E : IntermediateField K (AlgebraicClosure K)) :
    IsAlgClosure E (AlgebraicClosure K) := by
  exact isAlgClosure_of_tower (K := K)

end ZInQ.Contrib.CloudR2NOS.Extension

#print axioms ZInQ.Contrib.CloudR2NOS.Extension.isAlgClosure_of_tower
#print axioms ZInQ.Contrib.CloudR2NOS.Extension.isAlgClosure_over_intermediateField
