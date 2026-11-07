import ZInQKernel.Compiler.Translation.NaturalCode
import ZInQKernel.Compiler.Translation.TranslateScope
import ZInQKernel.Syntax.Recipes.FixedScalar

/-!
# The callees of the translation in the template library

With the template library (`Syntax.templateLibrary`), the callees of a translated recipe are the
natural-code template (index `12`), raw addition (`1`), multiplication (`11`) and the fixed-scalar
templates `S_c` (`18 + h`). Under M and with the psi constructor read as the division-polynomial
components (`I.psi = psiComponent`), they have the callee semantics used by the translation
(`calleeSemantics_library`): the natural-code predicate, raw addition and multiplication on
canonical codes, and `Rel_{S_c}(ι(1), r) ⟺ r = ι(c)` for `c ≥ 2`.
-/

namespace ZInQ.Translation

open Compiler.Natural Syntax

variable {E : Type}

/-! ### Calls on lists of codes as calls on concatenated codes -/

theorem codeArgs_one (A : Fin 5 → ℚ) : (fun k : Fin 5 => codeArgs [A] k) = A := by
  funext k; fin_cases k <;> rfl

theorem codeArgs_two (A B : Fin 5 → ℚ) :
    (fun k : Fin 10 => codeArgs [A, B] k) = Fin.append A B := by
  funext k; fin_cases k <;> rfl

theorem codeArgs_three (A B C : Fin 5 → ℚ) :
    (fun k : Fin 15 => codeArgs [A, B, C] k) = Fin.append (Fin.append A B) C := by
  funext k; fin_cases k <;> rfl

theorem codeArgs_four (A B C D : Fin 5 → ℚ) :
    (fun k : Fin 20 => codeArgs [A, B, C, D] k) =
      Fin.append (Fin.append (Fin.append A B) C) D := by
  funext k; fin_cases k <;> rfl

/-! ### The library -/

variable (I : Constructors E) (cstar ell T c3 : ℤ)

theorem getEx_library_natural :
    getEx (templateLibrary I cstar ell T c3) 12 = naturalTemplate I cstar ell T := rfl

theorem getEx_library_rawAdd : getEx (templateLibrary I cstar ell T c3) 1 = rawAddTemplate := rfl

theorem getEx_library_multiply :
    getEx (templateLibrary I cstar ell T c3) 11 = multiplyTemplate I cstar ell T := rfl

/-- The fixed-scalar template of a constant of a prefix of the constant table. -/
theorem getEx_library_scalar {consts : List ℤ} (hc : consts <+: integerConstants c3) {c : ℤ}
    (hmem : c ∈ consts) :
    getEx (templateLibrary I cstar ell T c3) (18 + consts.idxOf c) = scalarTemplate I c := by
  have hlt : consts.idxOf c < consts.length := List.idxOf_lt_length_iff.2 hmem
  have h5 : consts.idxOf c < 5 := lt_of_lt_of_le hlt (by simpa [integerConstants] using hc.length_le)
  have := getEx_templateLibrary_scalar I cstar ell T c3 ⟨consts.idxOf c, h5⟩
  rw [this]
  congr 1
  simp only [List.get_eq_getElem]
  rw [← hc.getElem hlt, List.getElem_idxOf hlt]

/-- **The callee semantics of the library**, under M and with the division-polynomial psi
constructor. -/
theorem calleeSemantics_library (hI : I.psi = psiComponent)
    (hM : MultiplicationExact I cstar ell T) :
    CalleeSemantics (getEx (templateLibrary I cstar ell T c3) 12)
      (getEx (templateLibrary I cstar ell T c3) 1) (getEx (templateLibrary I cstar ell T c3) 11)
      (scalarTemplate I) where
  natural A := by
    show (naturalTemplate I cstar ell T).Rel (fun k : Fin 5 => codeArgs [A] k) ↔ _
    rw [codeArgs_one]
    exact natural_rel_iff hM A
  add a b R := by
    show rawAddTemplate.Rel (fun k : Fin 15 => codeArgs [iota a, iota b, R] k) ↔ _
    rw [codeArgs_three]
    exact rel_rawAdd_iota a b R
  mul a b R := by
    show (multiplyTemplate I cstar ell T).Rel
      (fun k : Fin 15 => codeArgs [iota a, iota b, R] k) ↔ _
    rw [codeArgs_three]
    exact hM.rel_iota_iff a b R
  scalar c hc R := by
    show (scalarTemplate I c).Rel (fun k : Fin 10 => codeArgs [iota 1, R] k) ↔ _
    rw [codeArgs_two, scalarTemplate_rel_iff_iota I hI (by omega), mul_one]

/-- The witness counts of the library callees. -/
theorem library_witnesses :
    (getEx (templateLibrary I cstar ell T c3) 12).witnesses = 140604 ∧
      (getEx (templateLibrary I cstar ell T c3) 1).witnesses = 6 ∧
      (getEx (templateLibrary I cstar ell T c3) 11).witnesses = 35134 := by
  rw [getEx_library_natural, getEx_library_rawAdd, getEx_library_multiply,
    naturalTemplate_witnesses, rawAddTemplate_witnesses, multiplyTemplate_witnesses]
  exact ⟨rfl, rfl, rfl⟩

end ZInQ.Translation
