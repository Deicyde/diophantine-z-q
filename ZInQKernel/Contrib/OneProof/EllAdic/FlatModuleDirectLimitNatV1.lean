import ZInQKernel.Contrib.OneProof.EllAdic.FlatSequenceRepresentativesV1
import Mathlib.Algebra.Colimit.Module

set_option autoImplicit false

namespace RC53.EllAdic

universe u v

variable {R : Type u} [CommRing R]
variable (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]

/-- Flatness on the literal quotient used for the module direct limit.
The representing maps and vanishing witnesses are its own `of` and
`of.zero_exact`, not data for a separately chosen colimit. -/
theorem flat_moduleDirectLimit_nat
    (f : ∀ i j, i ≤ j → M i →ₗ[R] M j) [DirectedSystem M (f · · ·)]
    (stageFlat : ∀ i, Module.Flat R (M i)) :
    Module.Flat R (Module.DirectLimit M f) :=
  flat_of_sequence_representatives M (fun h => f _ _ h) (Module.DirectLimit.of R ℕ M f)
    (fun _ _ => Module.DirectLimit.of_f) Module.DirectLimit.exists_of
    (fun _ _ h => Module.DirectLimit.of.zero_exact h) stageFlat

end RC53.EllAdic
