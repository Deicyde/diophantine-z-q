import ZInQKernel.Syntax.Templates.Multiply
import ZInQKernel.Syntax.Constants.Guard

/-!
# Semantics of the guard template for the guard polynomial of the specification

Blueprint: `syntax/templates/guard-semantics.md`.

`Syntax.guardTemplate_rel_iff_not_falseTriple` takes the zero set of `G_T` as a hypothesis. For
the guard polynomial of the specification, `G_T = guardPoly T` (`syntax/constants/guard-product.md`),
that hypothesis is `guardPoly_eval_eq_zero_iff` once the triple codes `tripleCode (a, b, c)` are
identified with the concatenated codes `codes3 (ι a) (ι b) (ι c)`.
-/

namespace ZInQ.Syntax

open MvPolynomial

variable {E : Type}

/-- Coordinate `5 i + k` of `codes3 P Q R` is coordinate `k` of the `i`-th code. -/
theorem codes3_apply (P Q R : Fin 5 → ℚ) (i : Fin 3) (k : Fin 5) :
    codes3 P Q R ⟨5 * i + k, by omega⟩ = ![P, Q, R] i k := by
  generalize hj : (⟨5 * i + k, by omega⟩ : Fin 15) = j
  have hv : j.val = 5 * i.val + k.val := by rw [← hj]
  fin_cases i
  · obtain rfl : j = Fin.castAdd 5 (Fin.castAdd 5 k) := Fin.ext (by simp at hv ⊢; omega)
    simp [codes3]
  · obtain rfl : j = Fin.castAdd 5 (Fin.natAdd 5 k) := Fin.ext (by simp at hv ⊢; omega)
    rw [codes3, Fin.append_left, Fin.append_right]; rfl
  · obtain rfl : j = Fin.natAdd 10 k := Fin.ext (by simp at hv ⊢; omega)
    simp [codes3]

/-- `codes3` is injective. -/
theorem codes3_inj {P Q R P' Q' R' : Fin 5 → ℚ} :
    codes3 P Q R = codes3 P' Q' R' ↔ P = P' ∧ Q = Q' ∧ R = R' := by
  refine ⟨fun h => ?_, fun ⟨h1, h2, h3⟩ => by rw [h1, h2, h3]⟩
  have key : ∀ (i : Fin 3) (k : Fin 5), ![P, Q, R] i k = ![P', Q', R'] i k := fun i k => by
    rw [← codes3_apply, ← codes3_apply, h]
  exact ⟨funext (key 0), funext (key 1), funext (key 2)⟩

/-- The triple code of `(a, b, c)` is the concatenation of `ι(a)`, `ι(b)`, `ι(c)`. -/
theorem tripleCode_eq_codes3 (a b c : ℤ) :
    tripleCode (a, b, c) = codes3 (iota a) (iota b) (iota c) := by
  symm
  rw [tripleCode_eq_iff]
  intro i k
  rw [codes3_apply]
  fin_cases i <;> rfl

/-- The rational zero set of the guard polynomial of the specification is the set of false
triples of codes in the box. -/
theorem guardPoly_eval_eq_zero_iff_falseTripleCodes (T : ℤ) (P : Fin 15 → ℚ) :
    eval₂ (Int.castRingHom ℚ) P (guardPoly T) = 0 ↔ FalseTripleCodes T P := by
  rw [guardPoly_eval_eq_zero_iff]
  simp only [FalseTripleCodes, tripleCode_eq_codes3]

/-- **Semantics of the guard template** for the guard polynomial of the specification: if the
guard constructor at `T` is `G_T = guardPoly T`, the guard holds exactly off the false triples
of codes in the box. -/
theorem guardTemplate_rel_iff_not_falseTriple_guardPoly (I : Constructors E) (T : ℤ)
    (hI : I.guard T = guardPoly T) (a : Fin 15 → ℚ) :
    (guardTemplate I T).Rel a ↔ ¬ FalseTripleCodes T a :=
  guardTemplate_rel_iff_not_falseTriple I T
    (fun P => by rw [hI]; exact guardPoly_eval_eq_zero_iff_falseTripleCodes T P) a

/-- **Semantics of the guard template**, in the form of the article: for all `P₀, P₁, P₂ ∈ ℚ⁵`,
`Rel_guard(P₀, P₁, P₂)` holds iff there is no `(a, b, c) ∈ ℤ³` with `|a|, |b|, |c| ≤ T`,
`ab ≠ c` and `(P₀, P₁, P₂) = (ι(a), ι(b), ι(c))`. -/
theorem guardTemplate_rel_codes3_iff (I : Constructors E) (T : ℤ)
    (hI : I.guard T = guardPoly T) (P₀ P₁ P₂ : Fin 5 → ℚ) :
    (guardTemplate I T).Rel (codes3 P₀ P₁ P₂) ↔
      ¬ ∃ a b c : ℤ, |a| ≤ T ∧ |b| ≤ T ∧ |c| ≤ T ∧ a * b ≠ c ∧
        P₀ = iota a ∧ P₁ = iota b ∧ P₂ = iota c := by
  rw [guardTemplate_rel_iff_not_falseTriple_guardPoly I T hI, FalseTripleCodes]
  simp only [codes3_inj]

end ZInQ.Syntax
