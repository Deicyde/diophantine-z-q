/-
STRUCTURAL MUST-FAIL: family index supplied without [Finite ι].
Expected: failure to synthesize Finite ι at the producer application.
This does not rule out an infinite-index family with independently finite range;
that is not the frozen F4 input contract. No arithmetic counterexample is claimed.
-/
import FCF_Proof
universe u
open ClimbFiniteCoefficientField

example {ι : Type u} (c : ι → Qbar) (ρ : Qbar →ₐ[ℚ] ℂ) :
    FiniteDimensional ℚ (familyField c) := by
  have h := finiteFamily_numberField_fixedPlace c ρ
  exact h.1
