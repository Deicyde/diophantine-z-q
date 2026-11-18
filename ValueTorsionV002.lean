import Mathlib.RingTheory.Valuation.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.FieldTheory.Minpoly.Finite

/-!
# Values of algebraic elements are torsion over the values of the base

For a valuation `v` on a field `M` and an element `x ≠ 0` algebraic over a subfield `K`, two
terms of maximal value in `minpoly K x` evaluated at `x` must tie (the ultrametric inequality
forbids a unique maximum of a vanishing sum). Hence some power `v(x)^k`, `1 ≤ k ≤ deg`, is a
ratio of values of nonzero elements of `K`. This is the step towards discreteness of a
valuation ring of a finite extension of a discretely valued field.
-/

noncomputable section
set_option autoImplicit false

namespace WildTameCharacter

open Polynomial

variable {K M : Type*} [Field K] [Field M] [Algebra K M]
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Two maximal terms tie.** -/
theorem exists_pow_val_eq_of_isIntegral (v : Valuation M Γ₀) {x : M} (hx : x ≠ 0)
    (hint : IsIntegral K x) :
    ∃ k : ℕ, 0 < k ∧ k ≤ (minpoly K x).natDegree ∧ ∃ a b : K, b ≠ 0 ∧
      v (algebraMap K M a) = v (algebraMap K M b) * v x ^ k := by
  classical
  set p := minpoly K x with hp
  set d := p.natDegree with hd
  have hmon : p.Monic := minpoly.monic hint
  have hd0 : 0 < d := minpoly.natDegree_pos hint
  set f : ℕ → M := fun i => algebraMap K M (p.coeff i) * x ^ i with hf
  have hsum : ∑ i ∈ Finset.range (d + 1), f i = 0 := by
    have h := minpoly.aeval K x
    rw [aeval_eq_sum_range] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hf, Algebra.smul_def]
  have hvx : v x ≠ 0 := (Valuation.ne_zero_iff v).2 hx
  have hfd : v (f d) ≠ 0 := by
    rw [hf]
    simp only [hd, hmon.coeff_natDegree, map_one, one_mul, map_pow]
    exact pow_ne_zero _ hvx
  obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image (Finset.range (d + 1)) (fun i => v (f i))
    ⟨d, Finset.self_mem_range_succ d⟩
  have hfj : v (f j) ≠ 0 := by
    intro h0
    have := hjmax d (Finset.self_mem_range_succ d)
    rw [h0] at this
    exact hfd (le_antisymm this zero_le)
  -- some other index ties with `j`
  have htie : ∃ i ∈ Finset.range (d + 1), i ≠ j ∧ v (f i) = v (f j) := by
    by_contra hne
    have hlt : ∀ i ∈ Finset.range (d + 1) \ {j}, v (f i) < v (f j) := by
      intro i hi
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
      refine lt_of_le_of_ne (hjmax i hi.1) fun heq => hne ⟨i, hi.1, hi.2, heq⟩
    have h := Valuation.map_sum_eq_of_lt v hj hlt
    rw [hsum, Valuation.map_zero] at h
    exact hfj h.symm
  obtain ⟨i, hi, hij, hvi⟩ := htie
  have hval : ∀ m : ℕ, v (f m) = v (algebraMap K M (p.coeff m)) * v x ^ m := fun m => by
    rw [hf, Valuation.map_mul, Valuation.map_pow]
  have hcoeff_ne : ∀ m : ℕ, v (f m) = v (f j) → p.coeff m ≠ 0 := by
    intro m hm h0
    rw [hval, h0, map_zero, Valuation.map_zero, zero_mul] at hm
    exact hfj hm.symm
  have hci : p.coeff i ≠ 0 := hcoeff_ne i hvi
  have hcj : p.coeff j ≠ 0 := hcoeff_ne j rfl
  have hile : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hjle : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rcases lt_or_gt_of_ne hij with h | h
  · -- i < j : v(a_i) v(x)^i = v(a_j) v(x)^j, cancel v(x)^i
    refine ⟨j - i, by omega, by omega, p.coeff i, p.coeff j, hcj, ?_⟩
    have e := hvi
    rw [hval, hval] at e
    have hxi : v x ^ i ≠ 0 := pow_ne_zero _ hvx
    have hsplit : v x ^ j = v x ^ (j - i) * v x ^ i := by
      rw [← pow_add, Nat.sub_add_cancel h.le]
    rw [hsplit, ← mul_assoc] at e
    exact mul_right_cancel₀ hxi e
  · refine ⟨i - j, by omega, by omega, p.coeff j, p.coeff i, hci, ?_⟩
    have e := hvi.symm
    rw [hval, hval] at e
    have hxj : v x ^ j ≠ 0 := pow_ne_zero _ hvx
    have hsplit : v x ^ i = v x ^ (i - j) * v x ^ j := by
      rw [← pow_add, Nat.sub_add_cancel h.le]
    rw [hsplit, ← mul_assoc] at e
    exact mul_right_cancel₀ hxj e

/-- In a finite extension the exponent is at most the degree. -/
theorem exists_pow_val_eq_of_finiteDimensional [FiniteDimensional K M] (v : Valuation M Γ₀)
    {x : M} (hx : x ≠ 0) :
    ∃ k : ℕ, 0 < k ∧ k ≤ Module.finrank K M ∧ ∃ a b : K, b ≠ 0 ∧
      v (algebraMap K M a) = v (algebraMap K M b) * v x ^ k := by
  have hint : IsIntegral K x := .of_finite K x
  obtain ⟨k, hk0, hkd, a, b, hb, h⟩ := exists_pow_val_eq_of_isIntegral v hx hint
  exact ⟨k, hk0, hkd.trans (minpoly.natDegree_le x), a, b, hb, h⟩

end WildTameCharacter
