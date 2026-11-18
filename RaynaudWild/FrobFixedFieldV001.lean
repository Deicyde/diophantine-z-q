import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Finiteness

/-!
# Fixed fields of residue Frobenius powers exhaust an algebraic extension of a finite field

Let `k` be a finite field with `q = |k|` elements, `Ω / k` an algebraic extension, and `σ` a
`k`-automorphism of `Ω` acting by `x ↦ x ^ q` (a residue Frobenius).

* `pow_apply_eq`: `σ ^ n` acts by `x ↦ x ^ (q ^ n)`;
* `exists_pow_card_pow_eq`: every `x ∈ Ω` satisfies `x ^ (q ^ d) = x` for some `d ≥ 1`
  (it lies in the finite field `k(x)`);
* `fixedFrob n`: the fixed field of `σ ^ n!`, a finite subfield containing `k`;
  `fixedFrob_mono` (an increasing chain) and `exists_mem_fixedFrob` (its union is `Ω`).
-/

namespace RaynaudWild.FrobDescent

variable {k Ω : Type} [Field k] [Finite k] [Field Ω] [Algebra k Ω]

/-- Every element of an algebraic extension of a finite field is fixed by some power `q ^ d`,
`d ≥ 1`, of the `q`-power map. -/
theorem exists_pow_card_pow_eq [Algebra.IsAlgebraic k Ω] (x : Ω) :
    ∃ d : ℕ, 0 < d ∧ x ^ (Nat.card k ^ d) = x := by
  classical
  haveI : Fintype k := Fintype.ofFinite k
  have hint : IsIntegral k x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  haveI : FiniteDimensional k (IntermediateField.adjoin k {x}) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite (IntermediateField.adjoin k {x}) := Module.finite_of_finite k
  haveI : Fintype (IntermediateField.adjoin k {x}) := Fintype.ofFinite _
  have hcard : Fintype.card (IntermediateField.adjoin k {x}) =
      Nat.card k ^ Module.finrank k (IntermediateField.adjoin k {x}) := by
    rw [Module.card_eq_pow_finrank (K := k), Nat.card_eq_fintype_card]
  refine ⟨Module.finrank k (IntermediateField.adjoin k {x}), Module.finrank_pos, ?_⟩
  have h := FiniteField.pow_card
    (⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : IntermediateField.adjoin k {x})
  rw [hcard] at h
  exact congrArg Subtype.val h

variable (σ : Ω ≃ₐ[k] Ω)

/-- `σ ^ n` acts by `x ↦ x ^ (q ^ n)`. -/
theorem pow_apply_eq (hσ : ∀ x : Ω, σ x = x ^ Nat.card k) (n : ℕ) (x : Ω) :
    (σ ^ n) x = x ^ (Nat.card k ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, hσ, ← pow_mul, pow_succ]

/-- If `σ` fixes `x` then so does every power. -/
theorem pow_apply_eq_self_of_apply_eq {τ : Ω ≃ₐ[k] Ω} {x : Ω} (h : τ x = x) (j : ℕ) :
    (τ ^ j) x = x := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', AlgEquiv.mul_apply, ih, h]

/-- The fixed field of `σ ^ n!`. -/
def fixedFrob (n : ℕ) : IntermediateField k Ω :=
  IntermediateField.fixedField (Subgroup.zpowers (σ ^ n.factorial))

theorem mem_fixedFrob_iff (n : ℕ) (x : Ω) : x ∈ fixedFrob σ n ↔ (σ ^ n.factorial) x = x := by
  rw [fixedFrob, IntermediateField.mem_fixedField_iff]
  constructor
  · intro h
    exact h _ (Subgroup.mem_zpowers _)
  · intro h f hf
    have hle : Subgroup.zpowers (σ ^ n.factorial) ≤ MulAction.stabilizer (Ω ≃ₐ[k] Ω) x := by
      rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
      exact h
    have hf' := hle hf
    rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at hf'
    exact hf'

/-- The fixed fields form an increasing chain. -/
theorem fixedFrob_mono {n m : ℕ} (hnm : n ≤ m) : fixedFrob σ n ≤ fixedFrob σ m := by
  intro x hx
  rw [mem_fixedFrob_iff] at hx ⊢
  obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial hnm
  rw [hc, pow_mul]
  exact pow_apply_eq_self_of_apply_eq hx c

/-- Their union is all of `Ω`. -/
theorem exists_mem_fixedFrob [Algebra.IsAlgebraic k Ω] (hσ : ∀ x : Ω, σ x = x ^ Nat.card k)
    (x : Ω) : ∃ n, x ∈ fixedFrob σ n := by
  obtain ⟨d, hd, hx⟩ := exists_pow_card_pow_eq (k := k) x
  refine ⟨d, ?_⟩
  rw [mem_fixedFrob_iff]
  obtain ⟨c, hc⟩ := Nat.dvd_factorial hd le_rfl
  rw [hc, pow_mul]
  apply pow_apply_eq_self_of_apply_eq
  rw [pow_apply_eq σ hσ, hx]

end RaynaudWild.FrobDescent
