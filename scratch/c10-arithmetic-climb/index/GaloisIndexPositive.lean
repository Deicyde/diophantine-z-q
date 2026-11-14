/-
climb/galois-index — positive case and boundary guards (NEW file, 2026-11-14).

Additive to `GaloisIndex.lean`, which is unchanged. Raised by the parent's precision note:

  * characteristic zero is SUFFICIENT for any number-field degree, but it is NOT logically
    necessary: positive characteristic also works whenever the characteristic does not divide
    the degree (`cast_index_ne_zero_of_charP_not_dvd` below). The `CharP`-divides lemmas in
    `GaloisIndex.lean` show that nonzero-ness of the index CAST cannot be dropped uniformly —
    they are not a proof that char 0 is required in every case;
  * `index_eq_zero_of_not_finiteDimensional` is a conditional lemma about an arbitrary
    infinite-dimensional intermediate field. It is NOT a constructed infinite-degree
    counterexample, and no such field is constructed here.

Constructed vs symbolic, explicitly:
  * CONSTRUCTED: the `L = ℚ`, `ι = Algebra.ofId ℚ ℚ̄` case — a concrete number field, a concrete
    embedding, the subgroup computed to be `⊤`, index `1`, cast `1`.
  * SYMBOLIC: the degree-2 / characteristic-2 guard and the `¬ p ∣ [L:ℚ]` lemma quantify over a
    number field of the stated degree and over a field of the stated characteristic; no
    quadratic field and no positive-characteristic coefficient field is constructed.
-/

import GaloisIndex

namespace ClimbGaloisIndexPositive

open ClimbGaloisIndex

/-! ## 1. CONSTRUCTED positive case: `L = ℚ` -/

/-- Every element of `G_ℚ` fixes `ℚ` pointwise, so the literal fixing subgroup of the rational
embedding is the whole group. -/
theorem fixSub_rat : fixSub (Algebra.ofId ℚ Qbar) = ⊤ := by
  ext σ
  simp only [mem_fixSub_iff, Subgroup.mem_top, iff_true]
  intro a
  exact σ.commutes a

/-- Its index is `1`. -/
theorem index_fixSub_rat : (fixSub (Algebra.ofId ℚ Qbar)).index = 1 := by
  rw [fixSub_rat, Subgroup.index_top]

/-- …which is the general formula at `[ℚ:ℚ] = 1`. -/
theorem index_fixSub_rat_eq_finrank :
    (fixSub (Algebra.ofId ℚ Qbar)).index = Module.finrank ℚ ℚ := by
  rw [index_fixSub_rat, Module.finrank_self]

/-- The cast is `1`, hence nonzero in every field: the primitive is instantiated, not vacuous. -/
theorem cast_index_fixSub_rat (k : Type*) [Field k] :
    (((fixSub (Algebra.ofId ℚ Qbar)).index : ℕ) : k) = 1 := by
  rw [index_fixSub_rat, Nat.cast_one]

theorem cast_index_fixSub_rat_ne_zero (k : Type*) [Field k] :
    (((fixSub (Algebra.ofId ℚ Qbar)).index : ℕ) : k) ≠ 0 := by
  rw [cast_index_fixSub_rat]
  exact one_ne_zero

/-! ## 2. Characteristic zero is sufficient, not necessary -/

variable {L : Type} [Field L] [CharZero L] (ι : L →ₐ[ℚ] Qbar)

/-- **Positive characteristic also works when it does not divide the degree.** So `CharZero k` in
`cast_index_fixSub_ne_zero` is a convenient sufficient condition, not a logical necessity. -/
theorem cast_index_ne_zero_of_charP_not_dvd [NumberField L] (k : Type*) [Field k] (p : ℕ)
    [CharP k p] (hp : ¬ p ∣ Module.finrank ℚ L) : (((fixSub ι).index : ℕ) : k) ≠ 0 := by
  rw [index_fixSub]
  intro h
  exact hp ((CharP.cast_eq_zero_iff k p _).mp h)

/-- SYMBOLIC boundary guard: at degree 2 in characteristic 2 the index is finite (`= 2`) and yet
its cast vanishes. The guard is about INVERTIBILITY of a finite index, not about finiteness. -/
theorem char_two_quadratic_guard [NumberField L] (h2 : Module.finrank ℚ L = 2)
    (k : Type*) [Field k] [CharP k 2] :
    (fixSub ι).index = 2 ∧ (((fixSub ι).index : ℕ) : k) = 0 :=
  ⟨by rw [index_fixSub, h2], cast_index_eq_zero_of_char_two ι k h2⟩

/-- The same degree 2, in characteristic 3: the cast is nonzero, so the guard is genuinely about
`char ∣ degree` and not about positive characteristic as such. -/
theorem char_three_quadratic_ok [NumberField L] (h2 : Module.finrank ℚ L = 2)
    (k : Type*) [Field k] [CharP k 3] : (((fixSub ι).index : ℕ) : k) ≠ 0 := by
  refine cast_index_ne_zero_of_charP_not_dvd ι k 3 ?_
  rw [h2]
  decide

/-! ## 3. Checks -/

#check @fixSub_rat
#check @index_fixSub_rat
#check @cast_index_fixSub_rat_ne_zero
#check @cast_index_ne_zero_of_charP_not_dvd
#check @char_two_quadratic_guard
#check @char_three_quadratic_ok

#print axioms fixSub_rat
#print axioms index_fixSub_rat
#print axioms index_fixSub_rat_eq_finrank
#print axioms cast_index_fixSub_rat
#print axioms cast_index_fixSub_rat_ne_zero
#print axioms cast_index_ne_zero_of_charP_not_dvd
#print axioms char_two_quadratic_guard
#print axioms char_three_quadratic_ok

end ClimbGaloisIndexPositive
