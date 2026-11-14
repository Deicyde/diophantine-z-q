/-
STRUCTURAL MUST-FAIL: κ and columns are finite, but the row type has no Finite input.
Expected: failure to synthesize the required row-finiteness instance.
Finite κ alone is not the frozen F5 coordinate contract. This is not a claim
that every infinite-row matrix has infinite coefficient range.
-/
import FCF_Proof
universe u
open ClimbFiniteCoefficientField

example {R : Type u} (M : Matrix R (Fin 1) Qbar) (ρ : Qbar →ₐ[ℚ] ℂ) :
    FiniteDimensional ℚ (jointField (∅ : Set Qbar) (fun _ : Fin 1 => M)) := by
  have h := finiteScalars_and_matrixFamily_oneField
    (fun _ : Fin 1 => R) (fun _ : Fin 1 => Fin 1)
    (∅ : Set Qbar) Set.finite_empty (fun _ : Fin 1 => M) ρ
  exact h.2.1
