import ZInQKernel.Multiplication.Soundness.FiniteBox
import ZInQKernel.Multiplication.Certificate.Multiply

/-!
# Soundness of the multiplication template

Blueprint: `multiplication/soundness/soundness.md`.

Assume the six-contact estimate. If `Rel_multiply(Y₁, Y₂, Y₃)`, then
`(Y₁, Y₂, Y₃) = (ι(a), ι(b), ι(ab))` for some `a, b ∈ ℤ`. By the unfolding of the template,
`Yᵢ = ι(nᵢ)`, the unguarded certificate accepts the triple and the guard holds; a false triple
would lie in `[-T, T]³` by the finite-box deduction, where the guard rejects it.

The template is `multiplyTemplate I c_* ℓ₀ T` for a constructor meaning `I`; as in the
certificate's unfolding lemma, the semantics of the fixed-scalar template `S_{c_*}` (`hS`) and
the identification of the guard polynomial (`hI`) are hypotheses on `I`, and `M₀ ≥ 1` (proved in
the size chapter) is a hypothesis.
-/

namespace ZInQ.Mult

open Syntax

variable {E : Type}

/-- **Soundness of the multiplication template.** -/
theorem multiply_sound (hH : SixContactEstimate) (hM0 : 1 ≤ Syntax.M0) (I : Constructors E)
    (hS : ∀ (m : ℤ) (r : Fin 5 → ℚ), (scalarTemplate I (Syntax.cstar : ℤ)).Rel
      (Fin.append (iota m) r) ↔ r = iota (Syntax.cstar * m))
    (hI : I.guard (Syntax.T : ℤ) = guardPoly (Syntax.T : ℤ)) (Y₁ Y₂ Y₃ : Fin 5 → ℚ)
    (hY : (multiplyTemplate I (Syntax.cstar : ℤ) (Syntax.ell : ℤ) (Syntax.T : ℤ)).Rel
      (codes3 Y₁ Y₂ Y₃)) :
    ∃ a b : ℤ, Y₁ = iota a ∧ Y₂ = iota b ∧ Y₃ = iota (a * b) := by
  obtain ⟨n, rfl, rfl, rfl, hcert, hG⟩ := (multiply_rel_iff I _ _ _ hS _ _ _).mp hY
  by_cases hf : n 0 * n 1 = n 2
  · exact ⟨n 0, n 1, rfl, rfl, by rw [hf]⟩
  exfalso
  have e : (![iota (n 0), iota (n 1), iota (n 2)] : Fin 3 → Fin 5 → ℚ) = fun i => iota (n i) := by
    funext i; fin_cases i <;> rfl
  rw [e] at hcert
  have hbox := finite_box_of_heightCert hH hM0 n hf (by exact_mod_cast hcert)
  exact guard_false_triple I _ hI n (fun i => (hbox i).le) hf hG

end ZInQ.Mult
