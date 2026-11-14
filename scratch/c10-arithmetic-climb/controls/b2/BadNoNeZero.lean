/-
STRUCTURAL MUST-FAIL: omit the actual NeZero N certificate.
Expected missing NeZero N instance, not parser/import failure.
This is not a claim that every zero-level character has infinite range.
-/
import B2PackingProof
open ClimbB2CoefficientPacking

example (N : ℕ) (χ₀ : DirichletCharacter Qbar N) : (characterValues χ₀).Finite := by
  exact characterValues_finite χ₀
