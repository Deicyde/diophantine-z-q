import ZInQKernel.Size.Norms.Coordinates
import ZInQKernel.Syntax.Constants.Guard

/-!
# Size of the guard polynomial

Blueprint: `size/norms/guard-size.md`.

`G_T` is a product of at most `(2T + 1)³ ≤ 8(T + 1)³` factors, one for each false triple in
`[-T, T]³`. By the heights of the codes, each factor `∑_j (D X_j - (D/B_j) A_j)²` has degree at
most `2` and norm at most `2^{32K + 6}`, `K = 2^30 (T + 1)³`, so `deg G_T ≤ 16 (T + 1)³` and
`‖G_T‖₁ ≤ 2^{2^39 (T+1)⁶}` (`guardPoly_size`). The polynomial is never expanded.
-/

namespace ZInQ.Size

open MvPolynomial
open ZInQ.Syntax (l1 l1_C l1_X l1_sub_le l1_pow_le l1_finset_sum_le l1_finset_prod_le guardPoly
  guardFactor falseTriples guardBox tripleCode tripleDen mem_falseTriples tripleCode_apply)

private theorem natAbs_le_of_abs_le {a : ℤ} {T : ℕ} (h : |a| ≤ T) : a.natAbs ≤ T := by
  rw [Int.abs_eq_natAbs] at h; exact_mod_cast h

/-- The coordinates of the triple code of a false triple have reduced numerators and
denominators at most `2^K`. -/
theorem tripleCode_height (T : ℕ) {t : ℤ × ℤ × ℤ} (ht : t ∈ falseTriples T) (j : Fin 15) :
    (tripleCode t j).num.natAbs ≤ 2 ^ (2 ^ 30 * (T + 1) ^ 3) ∧
      (tripleCode t j).den ≤ 2 ^ (2 ^ 30 * (T + 1) ^ 3) := by
  obtain ⟨a, b, c⟩ := t
  obtain ⟨ha, hb, hc, -⟩ := mem_falseTriples.1 ht
  have hi : ∀ i : Fin 3, (![a, b, c] i).natAbs ≤ T := by
    intro i
    fin_cases i
    · exact natAbs_le_of_abs_le ha
    · exact natAbs_le_of_abs_le hb
    · exact natAbs_le_of_abs_le hc
  have hj : j = ⟨5 * (⟨j / 5, by omega⟩ : Fin 3) + (⟨j % 5, by omega⟩ : Fin 5), by omega⟩ :=
    Fin.ext (by simp only; omega)
  rw [hj, tripleCode_apply]
  exact iota_coord_height T _ (hi _) _

/-- The number of false triples is at most `8 (T + 1)³`. -/
theorem card_falseTriples_le (T : ℕ) : (falseTriples T).card ≤ 8 * (T + 1) ^ 3 := by
  refine (Finset.card_filter_le _ _).trans ?_
  rw [guardBox, Finset.card_product, Finset.card_product, Int.card_Icc]
  have h : ((T : ℤ) + 1 - -(T : ℤ)).toNat = 2 * T + 1 := by omega
  rw [h, ← pow_three]
  calc (2 * T + 1) ^ 3 ≤ (2 * (T + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    _ = 8 * (T + 1) ^ 3 := by ring

/-- A factor of `G_T` has degree at most `2`. -/
theorem totalDegree_guardFactor_le (t : ℤ × ℤ × ℤ) : (guardFactor t).totalDegree ≤ 2 := by
  refine totalDegree_finsetSum_le fun j _ => (totalDegree_pow _ _).trans ?_
  have : (C (tripleDen t : ℤ) * X j -
      C (((tripleDen t / (tripleCode t j).den : ℕ) : ℤ) * (tripleCode t j).num) :
        MvPolynomial (Fin 15) ℤ).totalDegree ≤ 1 := by
    refine (totalDegree_sub _ _).trans (max_le ?_ (by rw [totalDegree_C]; omega))
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X]
  omega

/-- A factor of `G_T` for a false triple has norm at most `2^{32K + 6}`. -/
theorem l1_guardFactor_le (T : ℕ) {t : ℤ × ℤ × ℤ} (ht : t ∈ falseTriples T) :
    l1 (guardFactor t) ≤ 2 ^ (32 * (2 ^ 30 * (T + 1) ^ 3) + 6) := by
  set K := 2 ^ 30 * (T + 1) ^ 3
  have hD : tripleDen t ≤ 2 ^ (15 * K) := by
    rw [tripleDen, mul_comm, pow_mul]
    refine (Finset.prod_le_pow_card _ _ _ fun j _ => (tripleCode_height T ht j).2).trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
  have hterm : ∀ j, l1 ((C (tripleDen t : ℤ) * X j -
      C (((tripleDen t / (tripleCode t j).den : ℕ) : ℤ) * (tripleCode t j).num)) ^ 2) ≤
        2 ^ (32 * K + 2) := by
    intro j
    refine (l1_pow_le _ _).trans ?_
    have h1 : l1 (C (tripleDen t : ℤ) * X j : MvPolynomial (Fin 15) ℤ) ≤ 2 ^ (15 * K) := by
      rw [l1_C_mul, l1_X, Int.natAbs_natCast, mul_one]; exact hD
    have h2 : l1 (C (((tripleDen t / (tripleCode t j).den : ℕ) : ℤ) * (tripleCode t j).num) :
        MvPolynomial (Fin 15) ℤ) ≤ 2 ^ (15 * K) * 2 ^ K := by
      rw [l1_C, Int.natAbs_mul, Int.natAbs_natCast]
      exact Nat.mul_le_mul ((Nat.div_le_self _ _).trans hD) (tripleCode_height T ht j).1
    have h3 := (l1_sub_le _ _).trans (Nat.add_le_add h1 h2)
    calc _ ≤ (2 ^ (15 * K) + 2 ^ (15 * K) * 2 ^ K) ^ 2 := Nat.pow_le_pow_left h3 2
      _ ≤ (2 ^ (16 * K + 1)) ^ 2 := by
          refine Nat.pow_le_pow_left ?_ 2
          rw [← pow_add, show 16 * K + 1 = (15 * K + K) + 1 by ring, pow_succ]
          have : 2 ^ (15 * K) ≤ 2 ^ (15 * K + K) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
      _ = 2 ^ (32 * K + 2) := by rw [← pow_mul]; ring_nf
  refine (l1_finset_sum_le _ _).trans ?_
  calc _ ≤ ∑ _j : Fin 15, 2 ^ (32 * K + 2) := Finset.sum_le_sum fun j _ => hterm j
    _ = 15 * 2 ^ (32 * K + 2) := by simp
    _ ≤ 2 ^ 4 * 2 ^ (32 * K + 2) := Nat.mul_le_mul_right _ (by norm_num)
    _ = 2 ^ (32 * K + 6) := by rw [← pow_add]; ring_nf

/-- **Size of the guard polynomial.** For every integer `T ≥ 0`,
`deg G_T ≤ 16 (T + 1)³` and `‖G_T‖₁ ≤ 2^{2^39 (T+1)⁶}`. -/
theorem guardPoly_size (T : ℕ) :
    (guardPoly T).totalDegree ≤ 16 * (T + 1) ^ 3 ∧
      l1 (guardPoly T) ≤ 2 ^ (2 ^ 39 * (T + 1) ^ 6) := by
  have hcard := card_falseTriples_le T
  constructor
  · refine (totalDegree_finsetProd _ _).trans ?_
    calc _ ≤ ∑ _t ∈ falseTriples T, 2 := Finset.sum_le_sum fun t _ => totalDegree_guardFactor_le t
      _ = 2 * (falseTriples T).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ 16 * (T + 1) ^ 3 := by omega
  · refine (l1_finset_prod_le _ _).trans ?_
    refine (Finset.prod_le_pow_card _ _ _ fun t ht => l1_guardFactor_le T ht).trans ?_
    rw [← pow_mul]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    set S := (T + 1) ^ 3 with hS
    have hS1 : 1 ≤ S := Nat.one_le_pow _ _ (by omega)
    have h6 : (T + 1) ^ 6 = S * S := by rw [hS]; ring
    rw [h6]
    calc (32 * (2 ^ 30 * S) + 6) * (falseTriples T).card ≤ (32 * (2 ^ 30 * S) + 6) * (8 * S) :=
          Nat.mul_le_mul_left _ hcard
      _ ≤ 2 ^ 39 * (S * S) := by nlinarith

end ZInQ.Size
