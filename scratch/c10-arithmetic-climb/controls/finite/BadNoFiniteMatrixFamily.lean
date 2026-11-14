/-
STRUCTURAL MUST-FAIL: matrix-family index κ has no Finite input; rows/columns are Fin 1.
Expected: failure to synthesize Finite κ at the F5 producer application.
This does not rule out an infinite-index family with independently finite range.
No arithmetic necessity witness or counterexample is constructed.
-/
import FCF_Proof
universe u
open ClimbFiniteCoefficientField

example {κ : Type u} (M : (k : κ) → Matrix (Fin 1) (Fin 1) Qbar)
    (ρ : Qbar →ₐ[ℚ] ℂ) :
    FiniteDimensional ℚ (jointField (∅ : Set Qbar) M) := by
  have h := finiteScalars_and_matrixFamily_oneField
    (fun _ : κ => Fin 1) (fun _ : κ => Fin 1)
    (∅ : Set Qbar) Set.finite_empty M ρ
  exact h.2.1
