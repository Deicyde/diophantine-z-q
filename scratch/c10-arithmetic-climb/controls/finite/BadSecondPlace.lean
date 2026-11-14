/-
STRUCTURAL MUST-FAIL: use ρ' for the restriction but demand the unrelated caller ρ image.
Expected: equality type mismatch (the producer gives ρ' a, not ρ a).
No inequivalent-place witness is constructed; this tests the fixed-map contract.
-/
import FCF_Proof
open ClimbFiniteCoefficientField

example (a : Qbar) (ρ ρ' : Qbar →ₐ[ℚ] ℂ) :
    familyPlace (fun _ : Fin 1 => a) ρ'
      (familyLift (fun _ : Fin 1 => a) (0 : Fin 1)) = ρ a := by
  exact ((finiteFamily_numberField_fixedPlace (fun _ : Fin 1 => a) ρ').2.2.1
    (0 : Fin 1)).2
