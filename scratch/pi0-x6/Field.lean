import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.PowerBasis
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Tactic

noncomputable section

namespace Pi0X6

local notation "Qb" => AlgebraicClosure ℚ

open Polynomial IntermediateField

theorem not_isSquare_three_int (m : ℤ) : m * m ≠ 3 := by
  intro h
  have h1 : -2 < m := by nlinarith
  have h2 : m < 2 := by nlinarith
  interval_cases m <;> omega

theorem rat_sq_ne_three (q : ℚ) : q * q ≠ 3 := by
  intro h
  have hsq : IsSquare (3 : ℚ) := ⟨q, h.symm⟩
  rw [Rat.isSquare_iff] at hsq
  obtain ⟨⟨m, hm⟩, -⟩ := hsq
  exact not_isSquare_three_int m (by simpa using hm.symm)

/-- `ℚ(√−3)` contains no square root of `−1`. -/
theorem sqrt_neg_one_not_mem (z s : Qb) (hz : z ^ 2 = -1) (hs : s ^ 2 = -3) :
    z ∉ ℚ⟮s⟯ := by
  intro hmem
  have hint : IsIntegral ℚ s := Algebra.IsIntegral.isIntegral s
  let pb := IntermediateField.adjoin.powerBasis hint
  obtain ⟨f, hfdeg, hf⟩ := pb.exists_eq_aeval ⟨z, hmem⟩
  have hdim : pb.dim ≤ 2 := by
    rw [IntermediateField.adjoin.powerBasis_dim]
    have hp : (X ^ 2 + C (3 : ℚ)) ≠ 0 := by
      intro h0
      have := congrArg natDegree h0
      rw [natDegree_X_pow_add_C] at this
      simp at this
    have hdvd : minpoly ℚ s ∣ X ^ 2 + C (3 : ℚ) := by
      apply minpoly.dvd
      simp [hs]
    have := natDegree_le_of_dvd hdvd hp
    rwa [natDegree_X_pow_add_C] at this
  have hf1 : f.natDegree ≤ 1 := by omega
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hf1
  have hz' : z = (a : Qb) * s + (b : Qb) := by
    have := congrArg Subtype.val hf
    simp only [map_add, map_mul, aeval_C, aeval_X] at this
    rw [this]
    simp [eq_ratCast, pb, IntermediateField.adjoin.powerBasis_gen]
  rw [hz'] at hz
  have key : ((2 * a * b : ℚ) : Qb) * s = ((-1 + 3 * a ^ 2 - b ^ 2 : ℚ) : Qb) := by
    push_cast
    linear_combination hz - (a : Qb) ^ 2 * hs
  by_cases hab : (2 * a * b : ℚ) = 0
  · rw [hab] at key
    simp only [Rat.cast_zero, zero_mul] at key
    have key' : (-1 + 3 * a ^ 2 - b ^ 2 : ℚ) = 0 := by exact_mod_cast key.symm
    rcases mul_eq_zero.1 hab with ha | hb
    · have ha0 : a = 0 := by linarith
      subst ha0; nlinarith [sq_nonneg b]
    · subst hb
      exact rat_sq_ne_three (3 * a) (by nlinarith)
  · set q : ℚ := (-1 + 3 * a ^ 2 - b ^ 2) / (2 * a * b)
    have hsq : s = (q : Qb) := by
      have hne : ((2 * a * b : ℚ) : Qb) ≠ 0 := by exact_mod_cast hab
      rw [show q = (-1 + 3 * a ^ 2 - b ^ 2) / (2 * a * b) from rfl, Rat.cast_div, ← key]
      field_simp
    rw [hsq] at hs
    have : q ^ 2 = -3 := by exact_mod_cast hs
    nlinarith [sq_nonneg q]

/-- **Galois input**: for `z² = −1` and `s² = −3` in `ℚ̄` there is `σ ∈ Aut(ℚ̄/ℚ)` fixing `s` and
moving `z` (so `Gal(ℚ̄/ℚ(√−3)) ⊄ Gal(ℚ̄/ℚ(i))`). -/
theorem exists_fix_moves (z s : Qb) (hz : z ^ 2 = -1) (hs : s ^ 2 = -3) :
    ∃ σ : Qb ≃ₐ[ℚ] Qb, σ s = s ∧ σ z ≠ z := by
  by_contra h
  push Not at h
  apply sqrt_neg_one_not_mem z s hz hs
  rw [← InfiniteGalois.fixedField_fixingSubgroup ℚ⟮s⟯]
  intro σ
  apply h σ.1
  exact σ.2 ⟨s, IntermediateField.mem_adjoin_simple_self ℚ s⟩

end Pi0X6
