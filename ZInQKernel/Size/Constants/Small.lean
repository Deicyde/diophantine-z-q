import ZInQKernel.Syntax.Constants.Relations
import ZInQKernel.Size.Constants.Pow

/-!
# Small explicit bounds

Blueprint: `size/constants/small-constant-bounds.md`.

`P_s < 2^433`, `10^5 < W < 2^435 < 2^512`, `2^2000 < 324! < 2^2250` and `G₀ < 2^37`. These are
closed comparisons between explicit numbers of at most `2250` binary digits: the primorial is
replaced by its kernel-checked decimal literal, `324!` is evaluated by the kernel (`324`
multiplications), and the comparisons are decided with the kernel's GMP `Nat` operations.
-/

namespace ZInQ.Size

open Syntax AmbientPow

set_option exponentiation.threshold 512 in
theorem Ps_lt : Ps < 2 ^ 433 := by
  rw [Ps_eq_literal]; decide

theorem W_gt : 10 ^ 5 < W := by
  rw [W_eq_literal]; decide

set_option exponentiation.threshold 512 in
theorem W_lt : W < 2 ^ 435 := by
  rw [W_eq_literal]; decide

set_option exponentiation.threshold 512 in
theorem W_lt_two_pow_512 : W < 2 ^ 512 :=
  W_lt.trans (natPow_lt_natPow_right (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option exponentiation.threshold 2250 in
theorem F_bounds : 2 ^ 2000 < F ∧ F < 2 ^ 2250 := by
  rw [F_eq]; decide

theorem G0_lt : G0 < 2 ^ 37 := by
  rw [G0_eq]; decide

set_option exponentiation.threshold 512 in
/-- The small explicit bounds of the blueprint, in one statement. -/
theorem small_constant_bounds :
    Ps < 2 ^ 433 ∧ 10 ^ 5 < W ∧ W < 2 ^ 435 ∧ (2 : ℕ) ^ 435 < 2 ^ 512 ∧
      2 ^ 2000 < F ∧ F < 2 ^ 2250 ∧ G0 < 2 ^ 37 :=
  ⟨Ps_lt, W_gt, W_lt, natPow_lt_natPow_right (by decide) (by decide), F_bounds.1, F_bounds.2,
    G0_lt⟩

end ZInQ.Size
