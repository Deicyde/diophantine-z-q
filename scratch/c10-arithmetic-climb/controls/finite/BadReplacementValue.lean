/-
STRUCTURAL MUST-FAIL: replace the GIVEN a by unrelated b in value recovery.
Expected: equality type mismatch (the producer recovers a, not b).
No a≠b witness is constructed and no arithmetic counterexample is claimed.
-/
import FCF_Proof
open ClimbFiniteCoefficientField

example (a b : Qbar) (ρ : Qbar →ₐ[ℚ] ℂ) :
    (familyField (fun _ : Fin 1 => a)).val
      (familyLift (fun _ : Fin 1 => a) (0 : Fin 1)) = b := by
  exact ((finiteFamily_numberField_fixedPlace (fun _ : Fin 1 => a) ρ).2.2.1
    (0 : Fin 1)).1
