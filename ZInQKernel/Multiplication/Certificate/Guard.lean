import ZInQKernel.Syntax.Templates.Multiply
import ZInQKernel.Syntax.Constants.Guard
import ZInQKernel.Cleanup.GuardSemantics
import ZInQKernel.Model.Generator.InfiniteOrder

/-!
# The guard passes true triples and rejects false triples in the box

Blueprint: `multiplication/certificate/guard-true-triples.md`, discharging the hypothesis of
`syntax/templates/guard-semantics.md`.

The guard template `guardTemplate I T` evaluates the constructor `I.guard T`. When it is the
false-triple product `G_T = guardPoly T` of the syntax chapter (`hI`), its rational zero set is
exactly the set of codes of false triples in the box (`guardPoly_zero_set`, from
`Syntax.guardPoly_eval_eq_zero_iff`), so

1. `Rel_guard(ι(a), ι(b), ι(ab))` for all `a, b ∈ ℤ` (`guard_true_triple`), by injectivity of
   codes (`ZInQ.iota_injective`, which needs no Mordell–Weil input);
2. `Rel_guard(ι(n₁), ι(n₂), ι(n₃))` fails for `|n_i| ≤ T`, `n₁n₂ ≠ n₃` (`guard_false_triple`).

`T` stays symbolic; the guard product is never expanded.
-/

namespace ZInQ.Mult

open MvPolynomial Syntax

variable {E : Type}

/-- The coordinates of three codes `ι(a), ι(b), ι(c)` in point-major order are `tripleCode`. -/
theorem codes3_iota (a b c : ℤ) : codes3 (iota a) (iota b) (iota c) = tripleCode (a, b, c) :=
  (tripleCode_eq_codes3 a b c).symm

/-- **The zero set of `G_T`** in the form of the guard semantics: it is the set of codes of
false triples in the box. -/
theorem guardPoly_zero_set (T : ℤ) (P : Fin 15 → ℚ) :
    eval₂ (Int.castRingHom ℚ) P (guardPoly T) = 0 ↔ FalseTripleCodes T P :=
  guardPoly_eval_eq_zero_iff_falseTripleCodes T P

/-- **Semantics of the guard template**, unconditionally for the false-triple product. -/
theorem guard_rel_iff (I : Constructors E) (T : ℤ) (hI : I.guard T = guardPoly T)
    (a : Fin 15 → ℚ) : (guardTemplate I T).Rel a ↔ ¬ FalseTripleCodes T a :=
  guardTemplate_rel_iff_not_falseTriple_guardPoly I T hI a

/-- **The guard passes true triples.** -/
theorem guard_true_triple (I : Constructors E) (T : ℤ) (hI : I.guard T = guardPoly T)
    (a b : ℤ) : (guardTemplate I T).Rel (codes3 (iota a) (iota b) (iota (a * b))) := by
  rw [guard_rel_iff I T hI]
  rintro ⟨a', b', c', -, -, -, hf, he⟩
  rw [codes3_iota, codes3_iota] at he
  have h := tripleCode_eq_iff.1 he
  have ha : iota a = iota a' := funext fun k => by
    have := h 0 k; rw [tripleCode_apply] at this; simpa using this
  have hb : iota b = iota b' := funext fun k => by
    have := h 1 k; rw [tripleCode_apply] at this; simpa using this
  have hc : iota (a * b) = iota c' := funext fun k => by
    have := h 2 k; rw [tripleCode_apply] at this; simpa using this
  rw [iota_injective ha, iota_injective hb] at hc
  exact hf (iota_injective hc)

/-- **The guard rejects false triples in the box.** -/
theorem guard_false_triple (I : Constructors E) (T : ℤ) (hI : I.guard T = guardPoly T)
    (n : Fin 3 → ℤ) (hn : ∀ i, |n i| ≤ T) (hf : n 0 * n 1 ≠ n 2) :
    ¬ (guardTemplate I T).Rel (codes3 (iota (n 0)) (iota (n 1)) (iota (n 2))) := by
  rw [guard_rel_iff I T hI, not_not]
  exact ⟨n 0, n 1, n 2, hn 0, hn 1, hn 2, hf, rfl⟩

end ZInQ.Mult
