import ZInQKernel.Compiler.Translation.FourSquares
import ZInQKernel.Compiler.Translation.Points
import ZInQKernel.Syntax.Templates.Multiply
import ZInQKernel.Model.Generator

/-!
# The natural-code predicate

The multiplication statement M in its all-input form, for the multiplication template with
fixed constants `c_*`, `ℓ`, `T`: `Rel_multiply(p, q, r)` holds exactly when `p = ι(a)`,
`q = ι(b)` and `r = ι(ab)` for some integers `a, b` (`MultiplicationExact`). The multiplication
chapter proves it; here it is a hypothesis.

Under M, the natural-code template accepts exactly the codes of the natural numbers
(`natural_rel_iff`): its four square roots are typed by the multiplication calls before their
squares are added, so the three raw additions receive canonical codes; conversely Lagrange's
theorem writes every natural number as a sum of four squares.

(Blueprint: `compiler/translation/natural-code-semantics.md`.)
-/

namespace ZInQ.Translation

open Syntax

variable {E : Type}

/-- **The multiplication statement M** (all-input form): for all `p, q, r ∈ ℚ⁵`,
`Rel_multiply(p, q, r) ⟺ ∃ a b ∈ ℤ, p = ι(a) ∧ q = ι(b) ∧ r = ι(ab)`. -/
def MultiplicationExact (I : Constructors E) (cstar ell T : ℤ) : Prop :=
  ∀ p q r : Fin 5 → ℚ, (multiplyTemplate I cstar ell T).Rel (Fin.append (Fin.append p q) r) ↔
    ∃ a b : ℤ, p = iota a ∧ q = iota b ∧ r = iota (a * b)

/-- Under M, a multiplication call on `(p, p, r)` squares the index of `p`. -/
theorem MultiplicationExact.rel_sq_iff {I : Constructors E} {cstar ell T : ℤ}
    (hM : MultiplicationExact I cstar ell T) (p r : Fin 5 → ℚ) :
    (multiplyTemplate I cstar ell T).Rel (Fin.append (Fin.append p p) r) ↔
      ∃ a : ℤ, p = iota a ∧ r = iota (a * a) := by
  rw [hM]
  constructor
  · rintro ⟨a, b, ha, hb, hr⟩
    obtain rfl : a = b := iota_injective (ha.symm.trans hb)
    exact ⟨a, ha, hr⟩
  · rintro ⟨a, ha, hr⟩
    exact ⟨a, a, ha, ha, hr⟩

/-- Under M, a multiplication call on canonical codes gives the code of the product. -/
theorem MultiplicationExact.rel_iota_iff {I : Constructors E} {cstar ell T : ℤ}
    (hM : MultiplicationExact I cstar ell T) (a b : ℤ) (r : Fin 5 → ℚ) :
    (multiplyTemplate I cstar ell T).Rel (Fin.append (Fin.append (iota a) (iota b)) r) ↔
      r = iota (a * b) := by
  rw [hM]
  constructor
  · rintro ⟨a', b', ha, hb, hr⟩
    rw [iota_injective ha, iota_injective hb]
    exact hr
  · intro hr
    exact ⟨a, b, rfl, rfl, hr⟩

theorem lift_multiply_call (I : Constructors E) (cstar ell T : ℤ) (y : ℕ → ℚ) (A B D : Code)
    (w : ℕ) :
    (Formula.call (multiplyTemplate I cstar ell T) (Fin.append (Fin.append A B) D) w).Lift y ↔
      (multiplyTemplate I cstar ell T).Rel (Fin.append (Fin.append (fun i => ev y (A i))
        (fun i => ev y (B i))) (fun i => ev y (D i))) := by
  refine (Formula.lift_call _ _ _ _).trans ?_
  show (multiplyTemplate I cstar ell T).Rel
    (fun k : Fin (5 + 5 + 5) => ev y (Fin.append (Fin.append A B) D k)) ↔ _
  rw [ev_comp_append, ev_comp_append]

theorem lift_rawAdd_call (y : ℕ → ℚ) (A B D : Code) (w : ℕ) :
    (Formula.call rawAddTemplate (Fin.append (Fin.append A B) D) w).Lift y ↔
      rawAddTemplate.Rel (Fin.append (Fin.append (fun i => ev y (A i))
        (fun i => ev y (B i))) (fun i => ev y (D i))) := by
  refine (Formula.lift_call _ _ _ _).trans ?_
  show rawAddTemplate.Rel
    (fun k : Fin (5 + 5 + 5) => ev y (Fin.append (Fin.append A B) D k)) ↔ _
  rw [ev_comp_append, ev_comp_append]

/-- **The natural-code predicate.** Under M, for every `A ∈ ℚ⁵` (not assumed to be a code),
`Rel_natural(A) ⟺ A = ι(n)` for some `n ∈ ℕ`. -/
theorem natural_rel_iff {I : Constructors E} {cstar ell T : ℤ}
    (hM : MultiplicationExact I cstar ell T) (A : Fin 5 → ℚ) :
    (naturalTemplate I cstar ell T).Rel A ↔ ∃ n : ℕ, A = iota n := by
  rw [naturalTemplate_rel_iff]
  simp only [naturalFormula, Formula.lift_and, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, lift_multiply_call, lift_rawAdd_call, ev_varPoint]
  change (∃ y : ℕ → ℚ, (∀ i : Fin 5, y i = A i) ∧ _) ↔ _
  constructor
  · rintro ⟨y, hyA, h0, h1, h2, h3, h4, h5, h6⟩
    obtain ⟨a0, -, e0⟩ := hM.rel_sq_iff _ _ |>.1 h0
    obtain ⟨a1, -, e1⟩ := hM.rel_sq_iff _ _ |>.1 h1
    obtain ⟨a2, -, e2⟩ := hM.rel_sq_iff _ _ |>.1 h2
    obtain ⟨a3, -, e3⟩ := hM.rel_sq_iff _ _ |>.1 h3
    rw [e0, e1, rel_rawAdd_iota] at h4
    rw [h4, e2, rel_rawAdd_iota] at h5
    rw [h5, e3, rel_rawAdd_iota] at h6
    have hA : A = iota (a0 * a0 + a1 * a1 + a2 * a2 + a3 * a3) := by
      rw [← h6]; funext i; simp [hyA]
    refine ⟨(a0 * a0 + a1 * a1 + a2 * a2 + a3 * a3).toNat, ?_⟩
    rw [hA, Int.toNat_of_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_self_nonneg _)
      (mul_self_nonneg _)) (mul_self_nonneg _)) (mul_self_nonneg _))]
  · rintro ⟨n, rfl⟩
    obtain ⟨a0, a1, a2, a3, hn⟩ := four_squares n
    let s1 : ℤ := (a0 : ℤ) * a0 + (a1 : ℤ) * a1
    let s2 : ℤ := s1 + (a2 : ℤ) * a2
    let L : List (ℕ × (Fin 5 → ℚ)) := [(0, iota n), (5, iota a0), (10, iota a1), (15, iota a2),
      (20, iota a3), (25, iota ((a0 : ℤ) * a0)), (30, iota ((a1 : ℤ) * a1)),
      (35, iota ((a2 : ℤ) * a2)), (40, iota ((a3 : ℤ) * a3)), (140581, iota s1),
      (140592, iota s2)]
    have hL : (L.map Prod.fst).Pairwise Separated := by
      simp only [L, List.map_cons, List.map_nil]; decide
    let y := writePoints (fun _ => 0) L
    have hp : ∀ r P, (r, P) ∈ L → (fun i : Fin 5 => y (r + i)) = P := fun r P h =>
      writePoints_point _ hL h
    refine ⟨y, fun i => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := congrFun (hp 0 (iota n) (by simp [L])) i
      simpa using this
    · rw [hp 5 (iota a0) (by simp [L]), hp 25 (iota ((a0 : ℤ) * a0)) (by simp [L])]
      exact (hM.rel_sq_iff _ _).2 ⟨_, rfl, rfl⟩
    · rw [hp 10 (iota a1) (by simp [L]), hp 30 (iota ((a1 : ℤ) * a1)) (by simp [L])]
      exact (hM.rel_sq_iff _ _).2 ⟨_, rfl, rfl⟩
    · rw [hp 15 (iota a2) (by simp [L]), hp 35 (iota ((a2 : ℤ) * a2)) (by simp [L])]
      exact (hM.rel_sq_iff _ _).2 ⟨_, rfl, rfl⟩
    · rw [hp 20 (iota a3) (by simp [L]), hp 40 (iota ((a3 : ℤ) * a3)) (by simp [L])]
      exact (hM.rel_sq_iff _ _).2 ⟨_, rfl, rfl⟩
    · rw [hp 25 (iota ((a0 : ℤ) * a0)) (by simp [L]), hp 30 (iota ((a1 : ℤ) * a1)) (by simp [L]), hp 140581 (iota s1) (by simp [L]),
        rel_rawAdd_iota]
    · rw [hp 140581 (iota s1) (by simp [L]), hp 35 (iota ((a2 : ℤ) * a2)) (by simp [L]), hp 140592 (iota s2) (by simp [L]),
        rel_rawAdd_iota]
    · rw [hp 140592 (iota s2) (by simp [L]), hp 40 (iota ((a3 : ℤ) * a3)) (by simp [L]), hp 0 (iota n) (by simp [L]),
        rel_rawAdd_iota, hn]
      congr 1
      simp only [s1, s2]
      push_cast
      ring

end ZInQ.Translation
