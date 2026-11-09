import ZInQKernel.Multiplication.Soundness.MultiplySound
import ZInQKernel.Multiplication.Completeness.Template
import ZInQKernel.Compiler.Translation.NaturalCode

/-!
# Correctness of the multiplication template

Blueprint: `multiplication/multiplication-template.md`.

Assume the six-contact estimate, pole completeness and the slope representation SR
(`SlopeRepresentation`, a consequence of 22P and of 22P₂). For the
constructors of the specification and the fixed constants `c_*`, `ℓ`, `T`, the multiplication
template accepts `(Y₁, Y₂, Y₃) ∈ (ℚ⁵)³` exactly when `(Y₁, Y₂, Y₃) = (ι(a), ι(b), ι(ab))` for some
`a, b ∈ ℤ` (`multiplication_exact`), and then `a` and `b` are unique
(`multiplication_exact_unique`, `multiplication_existsUnique`). This is input M of the assembly.

Soundness is `multiply_sound` (from H) and completeness `multiply_complete` (from PC and SR).
-/

namespace ZInQ.Mult

open Syntax

/-- **Correctness of the multiplication template** (input M): for all `Y₁, Y₂, Y₃ ∈ ℚ⁵`,
`Rel_multiply(Y₁, Y₂, Y₃) ⟺ ∃ a b ∈ ℤ, (Y₁, Y₂, Y₃) = (ι(a), ι(b), ι(ab))`. -/
theorem multiplication_exact (hH : SixContactMin) (hPC : PoleCompleteness)
    (h22 : SlopeRepresentation) :
    Translation.MultiplicationExact Syntax.specConstructors FixedConst.cstar.value
      FixedConst.ell.value FixedConst.T.value := by
  intro Y₁ Y₂ Y₃
  constructor
  · exact multiply_sound hH Y₁ Y₂ Y₃
  · rintro ⟨a, b, rfl, rfl, rfl⟩
    exact multiply_complete hPC h22 a b

/-- **Uniqueness of `a, b`** in the multiplication statement: if
`(Y₁, Y₂, Y₃) = (ι(a), ι(b), ι(ab)) = (ι(a'), ι(b'), ι(a'b'))`, then `a = a'` and `b = b'`
(injectivity of `ι`). -/
theorem multiplication_exact_unique {Y₁ Y₂ Y₃ : Fin 5 → ℚ} {a b a' b' : ℤ}
    (h : Y₁ = iota a ∧ Y₂ = iota b ∧ Y₃ = iota (a * b))
    (h' : Y₁ = iota a' ∧ Y₂ = iota b' ∧ Y₃ = iota (a' * b')) : a = a' ∧ b = b' :=
  ⟨iota_injective (h.1.symm.trans h'.1), iota_injective (h.2.1.symm.trans h'.2.1)⟩

/-- Input M with uniqueness: `Rel_multiply(Y₁, Y₂, Y₃)` holds exactly when there are unique
`a, b ∈ ℤ` with `(Y₁, Y₂, Y₃) = (ι(a), ι(b), ι(ab))`. -/
theorem multiplication_existsUnique (hH : SixContactMin) (hPC : PoleCompleteness)
    (h22 : SlopeRepresentation) (Y₁ Y₂ Y₃ : Fin 5 → ℚ) :
    (multiplyTemplate Syntax.specConstructors FixedConst.cstar.value FixedConst.ell.value
        FixedConst.T.value).Rel (Fin.append (Fin.append Y₁ Y₂) Y₃) ↔
      ∃! ab : ℤ × ℤ, Y₁ = iota ab.1 ∧ Y₂ = iota ab.2 ∧ Y₃ = iota (ab.1 * ab.2) := by
  rw [multiplication_exact hH hPC h22]
  constructor
  · rintro ⟨a, b, h⟩
    refine ⟨(a, b), h, fun ⟨a', b'⟩ h' => ?_⟩
    obtain ⟨rfl, rfl⟩ := multiplication_exact_unique h h'
    rfl
  · rintro ⟨⟨a, b⟩, h, -⟩
    exact ⟨a, b, h⟩

end ZInQ.Mult
