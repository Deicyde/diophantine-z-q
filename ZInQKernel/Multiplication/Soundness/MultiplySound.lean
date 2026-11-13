import ZInQKernel.Multiplication.Soundness.FiniteBox
import ZInQKernel.Multiplication.Certificate.Spec

/-!
# Soundness of the multiplication template

Blueprint: `multiplication/soundness/soundness.md`.

Assume the six-contact estimate. If `Rel_multiply(Y₁, Y₂, Y₃)`, then
`(Y₁, Y₂, Y₃) = (ι(a), ι(b), ι(ab))` for some `a, b ∈ ℤ`. By the unfolding of the template,
`Yᵢ = ι(nᵢ)`, the unguarded certificate accepts the triple and the guard holds; a false triple
would lie in `[-T, T]³` by the finite-box deduction, where the guard rejects it.

The template is `multiplyTemplate specConstructors c_* ℓ₀ T` with the values of the named
constants; they are rewritten to `Syntax.cstar`, `Syntax.ell`, `Syntax.T`
(`FixedConst.value_cstar`, …) and never evaluated.
-/

namespace ZInQ.Mult

open Syntax

/-- **Soundness of the multiplication template.** -/
theorem multiply_sound (hH : SixContactMin) (Y₁ Y₂ Y₃ : Fin 5 → ℚ)
    (hY : (multiplyTemplate specConstructors FixedConst.cstar.value FixedConst.ell.value
      FixedConst.T.value).Rel (codes3 Y₁ Y₂ Y₃)) :
    ∃ a b : ℤ, Y₁ = iota a ∧ Y₂ = iota b ∧ Y₃ = iota (a * b) := by
  rw [FixedConst.value_cstar, FixedConst.value_ell, FixedConst.value_T] at hY
  obtain ⟨n, rfl, rfl, rfl, hcert, hG⟩ :=
    (multiply_rel_iff specConstructors _ _ _ spec_scalar_cstar_rel_iff _ _ _).mp hY
  by_cases hf : n 0 * n 1 = n 2
  · exact ⟨n 0, n 1, rfl, rfl, by rw [hf]⟩
  exfalso
  have e : (![iota (n 0), iota (n 1), iota (n 2)] : Fin 3 → Fin 5 → ℚ) = fun i => iota (n i) := by
    funext i; fin_cases i <;> rfl
  rw [e] at hcert
  have hbox := finite_box_of_heightCert hH n hf (by exact_mod_cast hcert)
  exact guard_false_triple specConstructors _ rfl n (fun i => (hbox i).le) hf hG

end ZInQ.Mult
