/-
STRUCTURAL MUST-FAIL: κ and rows are finite, but the column type has no Finite input.
Expected: failure to synthesize the required column-finiteness instance.
Finite κ alone is not the frozen F5 coordinate contract. This is not a claim
that every infinite-column matrix has infinite coefficient range.
-/
import FCF_Proof
universe u
open ClimbFiniteCoefficientField

example {C : Type u} (M : Matrix (Fin 1) C Qbar) (ρ : Qbar →ₐ[ℚ] ℂ) :
    FiniteDimensional ℚ (jointField (∅ : Set Qbar) (fun _ : Fin 1 => M)) := by
  have h := finiteScalars_and_matrixFamily_oneField
    (fun _ : Fin 1 => Fin 1) (fun _ : Fin 1 => C)
    (∅ : Set Qbar) Set.finite_empty (fun _ : Fin 1 => M) ρ
  exact h.2.1
