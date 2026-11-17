import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic

/-!
# Concrete rational Hurwitz coordinates

These theorems construct the five integer coordinates appearing in the existing
`H29Split.IsHurwitz` definition. No alternate Hurwitz predicate is defined.
The entry module transports these concrete witnesses to that actual definition.
This file proves prerequisites only; it is not a proof of `TYZProp23Printed`.
-/

open scoped Quaternion

set_option autoImplicit false

namespace TYZSquareOddness

private theorem square_le_quarter {x : ℚ} (h : |x| ≤ 1 / 2) :
    x ^ 2 ≤ (1 / 4 : ℚ) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  have hp : 0 ≤ (1 / 2 - x) * (1 / 2 + x) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

private theorem square_lt_quarter {x : ℚ} (h : |x| < 1 / 2) :
    x ^ 2 < (1 / 4 : ℚ) := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp h
  have hp : 0 < (1 / 2 - x) * (1 / 2 + x) :=
    mul_pos (by linarith) (by linarith)
  nlinarith

private theorem half_integer_of_round_tie (x : ℚ)
    (h : |x - (round x : ℚ)| = 1 / 2) :
    ∃ k : ℤ, x = (k : ℚ) + 1 / 2 := by
  by_cases hn : 0 ≤ x - (round x : ℚ)
  · rw [abs_of_nonneg hn] at h
    exact ⟨round x, by linarith⟩
  · rw [abs_of_neg (lt_of_not_ge hn)] at h
    refine ⟨round x - 1, ?_⟩
    push_cast
    linarith

/-- The literal five integer coordinates of a Hurwitz approximation with
Hamilton norm error strictly less than one. -/
theorem exists_hurwitz_coordinates_norm_lt_one (q : ℍ[ℚ]) :
    ∃ a b c d e : ℤ,
      Quaternion.normSq
        (q - (⟨(a : ℚ) - (e : ℚ) / 2, (b : ℚ) + (e : ℚ) / 2,
          (c : ℚ) + (e : ℚ) / 2, (d : ℚ) + (e : ℚ) / 2⟩ : ℍ[ℚ])) < 1 := by
  have h0 := abs_sub_round q.re
  have h1 := abs_sub_round q.imI
  have h2 := abs_sub_round q.imJ
  have h3 := abs_sub_round q.imK
  have s0 := square_le_quarter h0
  have s1 := square_le_quarter h1
  have s2 := square_le_quarter h2
  have s3 := square_le_quarter h3
  by_cases hs : |q.re - (round q.re : ℚ)| < 1 / 2 ∨
      |q.imI - (round q.imI : ℚ)| < 1 / 2 ∨
      |q.imJ - (round q.imJ : ℚ)| < 1 / 2 ∨
      |q.imK - (round q.imK : ℚ)| < 1 / 2
  · refine ⟨round q.re, round q.imI, round q.imJ, round q.imK, 0, ?_⟩
    have hsum :
        (q.re - (round q.re : ℚ)) ^ 2 +
          (q.imI - (round q.imI : ℚ)) ^ 2 +
          (q.imJ - (round q.imJ : ℚ)) ^ 2 +
          (q.imK - (round q.imK : ℚ)) ^ 2 < 1 := by
      rcases hs with h | h | h | h
      · have := square_lt_quarter h
        nlinarith
      · have := square_lt_quarter h
        nlinarith
      · have := square_lt_quarter h
        nlinarith
      · have := square_lt_quarter h
        nlinarith
    simpa [Quaternion.normSq_def', Quaternion.re_sub, Quaternion.imI_sub,
      Quaternion.imJ_sub, Quaternion.imK_sub] using hsum
  · have e0 : |q.re - (round q.re : ℚ)| = 1 / 2 :=
      le_antisymm h0 (not_lt.mp (fun h => hs (Or.inl h)))
    have e1 : |q.imI - (round q.imI : ℚ)| = 1 / 2 :=
      le_antisymm h1 (not_lt.mp (fun h => hs (Or.inr (Or.inl h))))
    have e2 : |q.imJ - (round q.imJ : ℚ)| = 1 / 2 :=
      le_antisymm h2 (not_lt.mp (fun h => hs (Or.inr (Or.inr (Or.inl h)))))
    have e3 : |q.imK - (round q.imK : ℚ)| = 1 / 2 :=
      le_antisymm h3 (not_lt.mp (fun h => hs (Or.inr (Or.inr (Or.inr h)))))
    obtain ⟨a, ha⟩ := half_integer_of_round_tie q.re e0
    obtain ⟨b, hb⟩ := half_integer_of_round_tie q.imI e1
    obtain ⟨c, hc⟩ := half_integer_of_round_tie q.imJ e2
    obtain ⟨d, hd⟩ := half_integer_of_round_tie q.imK e3
    refine ⟨a + 1, b, c, d, 1, ?_⟩
    have hq : q =
        (⟨((a + 1 : ℤ) : ℚ) - (1 : ℚ) / 2, (b : ℚ) + 1 / 2,
          (c : ℚ) + 1 / 2, (d : ℚ) + 1 / 2⟩ : ℍ[ℚ]) := by
      apply Quaternion.ext <;> dsimp <;> push_cast <;> linarith
    rw [hq]
    norm_num

/-- Integral double coordinates and integral Hamilton norm force the literal
Hurwitz parity condition. This is a concrete coordinate construction, not an
assumption of maximality or an alternative order definition. -/
theorem exists_hurwitz_coordinates_of_double_integral_norm (q : ℍ[ℚ])
    (a b c d n : ℤ)
    (ha : 2 * q.re = (a : ℚ)) (hb : 2 * q.imI = (b : ℚ))
    (hc : 2 * q.imJ = (c : ℚ)) (hd : 2 * q.imK = (d : ℚ))
    (hn : Quaternion.normSq q = (n : ℚ)) :
    ∃ r s t u e : ℤ,
      q = (⟨(r : ℚ) - (e : ℚ) / 2, (s : ℚ) + (e : ℚ) / 2,
        (t : ℚ) + (e : ℚ) / 2, (u : ℚ) + (e : ℚ) / 2⟩ : ℍ[ℚ]) := by
  have ea : (a : ℚ) ^ 2 = 4 * q.re ^ 2 := by rw [← ha]; ring
  have eb : (b : ℚ) ^ 2 = 4 * q.imI ^ 2 := by rw [← hb]; ring
  have ec : (c : ℚ) ^ 2 = 4 * q.imJ ^ 2 := by rw [← hc]; ring
  have ed : (d : ℚ) ^ 2 = 4 * q.imK ^ 2 := by rw [← hd]; ring
  rw [Quaternion.normSq_def'] at hn
  have hsqQ : (a : ℚ) ^ 2 + (b : ℚ) ^ 2 + (c : ℚ) ^ 2 + (d : ℚ) ^ 2 =
      4 * (n : ℚ) := by nlinarith
  have hsq : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 4 * n := by exact_mod_cast hsqQ
  rcases Int.even_or_odd' a with ⟨a0, rfl | rfl⟩ <;>
    rcases Int.even_or_odd' b with ⟨b0, rfl | rfl⟩ <;>
    rcases Int.even_or_odd' c with ⟨c0, rfl | rfl⟩ <;>
    rcases Int.even_or_odd' d with ⟨d0, rfl | rfl⟩
  all_goals push_cast at ha hb hc hd
  all_goals first
    | (refine ⟨a0, b0, c0, d0, 0, ?_⟩
       apply Quaternion.ext <;> dsimp <;> norm_num <;> linarith)
    | (refine ⟨a0 + 1, b0, c0, d0, 1, ?_⟩
       apply Quaternion.ext <;> dsimp <;> push_cast <;> norm_num <;> linarith)
    | (exfalso; ring_nf at hsq; omega)

end TYZSquareOddness
