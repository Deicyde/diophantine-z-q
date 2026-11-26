module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic

/-! Cardinal arithmetic for the ramified prime ideal class homomorphism. -/

public section

namespace HDec.CMBranch.FowlerArithmetic

/-- A homomorphism from `t` independent squarefree choices with at most two kernel
members exhibits a subgroup of size divisible by `2^(t-1)` in the target. -/
theorem pow_pred_card_dvd_of_card_ker_le_two {S A : Type*}
    [Finite S] [Group A] (f : Multiplicative (S → ZMod 2) →* A)
    (hker : Nat.card f.ker ≤ 2) : 2 ^ (Nat.card S - 1) ∣ Nat.card A := by
  classical
  let := Fintype.ofFinite S
  have hdom : Nat.card (Multiplicative (S → ZMod 2)) = 2 ^ Nat.card S := by
    change Nat.card (S → ZMod 2) = _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fun]
    simp
  have hcount := Subgroup.card_ker_mul_card_range f
  rw [hdom] at hcount
  have hp : 0 < Nat.card f.ker := Nat.card_pos
  have hrange : 2 ^ (Nat.card S - 1) ∣ Nat.card f.range := by
    by_cases hk : Nat.card f.ker = 1
    · rw [hk, one_mul] at hcount
      rw [hcount]
      exact pow_dvd_pow 2 (Nat.sub_le _ _)
    · have hk' : Nat.card f.ker = 2 := by omega
      rw [hk'] at hcount
      cases hS : Nat.card S with
      | zero => simp
      | succ n =>
        rw [hS, pow_succ', Nat.mul_right_inj (by decide : 2 ≠ 0)] at hcount
        change 2 ^ (n + 1 - 1) ∣ Nat.card f.range
        simp only [Nat.add_sub_cancel, hcount, dvd_refl]
  exact hrange.trans f.range.card_subgroup_dvd_card

end HDec.CMBranch.FowlerArithmetic
